{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen
  ( codegen )
  where

-- accelerate
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, shapeType, rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Analysis.Exp
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Default
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists))
import Control.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Text.LLVM as LP
import Data.Array.Accelerate.LLVM.CodeGen.Loop (imapFromStepTo)
-- Imports for half-sized
import LLVM.AST.Type.Operand (Operand)

codegen :: String
        -> Env AccessGroundR env
        -> Clustered NativeOp args
        -> Args env args
        -> LLVM Native
           ( Int -- The size of the kernel data, shared by all threads working on this kernel.
           , Module (KernelType env))
codegen name env cluster args
 | flat@(FlatCluster shr idxLHS sizes dirs localR localLHS flatOps) <- toFlatClustered cluster args
 , parallelDepth <- flatClusterIndependentLoopDepth flat
 , Exists parallelShr <- shapeRFromRank parallelDepth =
  codeGenFunction linkage name type' (LLVM.Lam argTp "arg" . LLVM.Lam primType "locks_array" . LLVM.Lam primType "workassist.first_index") $ do
    extractEnv

    -- Before the parallel work of a kernel is started, we first run the function once.
    -- This first call will initialize kernel memory (SEE: Kernel Memory)
    -- and decide whether the runtime may try to let multiple threads work on this kernel.
    initBlock <- newBlock "init"
    finishBlock <- newBlock "finish" -- Finish function from the work assisting paper
    workBlock <- newBlock "work"
    _ <- switch (OP_Word64 workassistFirstIndex) workBlock [(0xFFFFFFFF, initBlock), (0xFFFFFFFE, finishBlock)]
    let hasPermute = hasNPermute flat

    if parallelDepth == 0 && rank shr /= 0 then do
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS
      let ((idxVar, direction, size), loops') = case loops of
            [] -> internalError "Expected at least one loop since rank shr /= 0"
            (l:ls) -> (l, ls)

      -- Holds the previous index
      prevIndex <- tupleAlloca (TupRsingle scalarTypeInt)
      -- Booleans used to interleave half-sized tiles
      mustFinish <- hoistAlloca BoolPrimType
      hasFinished <- hoistAlloca BoolPrimType
      
      -- Parallelise over first dimension using parallel folds or scans
      case parCodeGens (parCodeGen (isDescending direction) mustFinish) 0 $ opCodeGens opCodeGen flatOps of
        Nothing -> internalError "Could not generate code for a cluster. Does parCodeGen lack a case for a collective parallel operation?"
        Just (Exists parCodes) -> do
          let hasScan = parCodeGenHasMultipleTileLoops parCodes
          let tileSize =
                if rank shr > 1 then
                  32
                else if hasScan then
                  -- We need to choose a tile size such that the values in the
                  -- first tile loop (the reduce step of the chained scan) are
                  -- still in the cache during the second tile loop (the scan
                  -- step of the chained scan).
                  1024 
                  -- 4 -- only for debugging
                else
                  1024 * 16 -- TODO: Implement a better heuristic to choose the tile size

          let envs' = envs{
            envsLoopDepth = 0,
            envsDescending = isDescending direction
          }

          -- Kernel memory
          let memoryTp' = parCodeGenMemory parCodes
          let memoryTp = StructPrimType False memoryTp'
          kernelMem <- instr' $ PtrCast (PtrPrimType memoryTp defaultAddrSpace) kernelMem'

          setBlock initBlock
          do
            -- Number of tiles
            sizeAdd <- A.add numType size (A.liftInt $ tileSize - 1)
            OP_Int tileCount' <- A.quot TypeInt sizeAdd (A.liftInt tileSize)

            -- Make new env in which tile amount is known
            let envs'' = envs'{
              envsTileCount = tileCount'
            }

            -- Initialize kernel memory
            parCodeGenInitMemory kernelMem envs'' TupleIdxSelf parCodes
            -- Decide whether tileCount is large enough

            OP_Bool isSmall <- A.lt singleType (OP_Int tileCount') $ A.liftInt 2
            value <- instr' $ Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
            retval_ value

          setBlock finishBlock
          do
            -- Declare fused-away and dead arrays at level zero.
            -- This is for instance needed for `map (+1) $ fold ...`,
            -- or a scanl' or scanr' whose reduced value is not used (like in prescanl).
            envs'' <- bindLocals 0 envs'

            -- Number of tiles
            sizeAdd <- A.add numType size (A.liftInt $ tileSize - 1)
            OP_Int tileCount' <- A.quot TypeInt sizeAdd (A.liftInt tileSize)

            -- Make new env in which tile amount is known
            let envs''' = envs''{
              envsTileCount = tileCount'
            }

            -- Execute code for after the parallel work of this kernel, for
            -- instance to write the result of a fold to the output array.
            parCodeGenFinish kernelMem envs''' TupleIdxSelf parCodes
            retval_ $ scalar (scalarType @Word8) 0

          setBlock workBlock
          -- Number of tiles
          sizeAdd <- A.add numType size (A.liftInt $ tileSize - 1)
          OP_Int tileCount' <- A.quot TypeInt sizeAdd (A.liftInt tileSize)
          tileCount <- instr' $ BitCast scalarType tileCount'


          -- Make new env in which tile amount is known
          let envs'' = envs'{
            envsTileCount = tileCount'
          }

          -- Emit code to initialize a thread, and get the codes for the tile loops          
          tileLoops <- genParallel kernelMem envs'' TupleIdxSelf parCodes


          -- Declare fused away arrays
          -- Declare as a tile array if there are multiple tile loops,
          -- otherwise as a single value.
          -- TODO: We can make this more precise by tracking whether arrays are
          -- only used in one tile loop. These arrays can also be stored as a
          -- single value.

          -- Reset these values whenever you re-enter the workAssisting loop
          _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool False)
          _ <- instr' $ Store NonVolatile hasFinished $ op BoolPrimType (A.liftBool True)

          envs''' <- bindLocalsInTile (\_ -> not $ null $ ptOtherLoops tileLoops) 1 tileSize envs''
          workassistLoop workassistIndex workassistFirstIndex tileCount $ \seqMode tileIdx' -> do
            tileIdx <- instr' $ BitCast scalarType tileIdx'

            tileIdxAbsolute <- -- TODO: duplicate code
              -- For a scanr, convert low-to-high indices to high-to-low indices:
              -- The first block (with tileIdx 0) should now correspond with the last
              -- values of the array. We implement that by reversing the tile indices here.
              if isDescending direction then do
                i <- A.sub numType (OP_Int tileCount') (OP_Int tileIdx)
                OP_Int j <- A.sub numType i (A.liftInt 1)
                return j
              else
                return tileIdx
            lower <- A.mul numType (OP_Int tileIdxAbsolute) (A.liftInt tileSize)
            upper' <- A.add numType lower (A.liftInt tileSize)
            upper <- A.min singleType upper' size

            -- If there is only a single tile loop (i.e. no parallel scans),
            -- then we don't generate code for a single-threaded mode:
            -- the default mode already is as fast as a single-threaded mode.
            let seqMode' = if null (ptOtherLoops tileLoops) then boolean False else seqMode

            -- CHANGE THIS BACK TODO: seqMode should not be this way forced
            -- set seqMode to True if tileIdx is 0, otherwise set it to false (for testing)
            -- seqModes' <- A.eq singleType (OP_Int tileIdx) (A.liftInt 0)
            -- let OP_Bool seqMode' = seqModes'

            let envs'''' = envs'''{
                envsTileIndex = OP_Int tileIdx
              }

          

            -- Note: ifThenElse' does not generate code for the then-branch if
            -- the condition is a constant. Thus, if a kernel does not have a
            -- scan, we won't generate separate code for a single-threaded mode.
            _ <- A.ifThenElse' (TupRunit, OP_Bool seqMode')
              -- Sequential mode
              (do
                let tileLoop = ptSingleThreaded tileLoops
                let ann =
                      -- Only do loop peeling if requested and when there are no nested loops.
                      -- Peeling over nested loops causes a lot of code duplication,
                      -- and is probably not worth it.
                      [ Loop.LoopPeel | ptPeel tileLoop && null loops' ]
                      -- We can use LoopNonEmpty since we
                      -- know that each tile is non-empty.
                      -- We cannot vectorize this loop (yet), as LLVM cannot vectorize loops
                      -- containing scans. We should either wait until LLVM supports this,
                      -- or vectorize loops (partially) ourselves.
                      -- As an alternative to vectorization, we ask LLVM to interleave the loop.
                      ++ [ Loop.LoopNonEmpty, Loop.LoopInterleave ]

                ptBefore tileLoop envs''''
                Loop.loopWith ann (isDescending direction) lower upper $ \isFirst idx -> do
                  localIdx <- A.sub numType idx lower
                  let envs''''' = envs''''{
                      envsLoopDepth = 1,
                      envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs'''',
                      envsIsFirst = isFirst,
                      envsTileLocalIndex = localIdx
                    }
                  genSequential envs''''' loops' $ ptIn tileLoop
                _ <- ptAfter tileLoop envs''''
                return OP_Unit
              )
              -- Parallel mode
              (do
                -- Hier de vorige environment opslaan

                forM_ ((True, ptFirstLoop tileLoops) : map (False, ) (ptOtherLoops tileLoops)) $ \(isFirstTileLoop, tileLoop) -> do
                  -- All nested loops are placed in the first tile loop by parCodeGens
                  let loops'' = if isFirstTileLoop then loops' else []
                  let ann =
                        -- Only do loop peeling if requested and when there are no nested loops.
                        -- Peeling over nested loops causes a lot of code duplication,
                        -- and is probably not worth it.
                        [ Loop.LoopPeel | ptPeel tileLoop && null loops'' ]
                        -- LLVM cannot vectorize loops containing scans (yet).
                        -- The first tile loop only does a reduction, others will perform a scan.
                        -- Loops containing permute (not permuteUnique) can
                        -- also not be vectorized.
                        -- Reduction cannot always be vectorized. This might in particular fail
                        -- on reductions of multiple values (tuples/pairs). For now, we thus do
                        -- not request vectorization, until we can reliably know whether LLVM can
                        -- vectorize something, or generate our code in a form that LLVM can
                        -- definitely vectorize.
                        ++ [ Loop.LoopInterleave ] -- Loop.LoopVectorize
                        -- We can use LoopNonEmpty since we
                        -- know that each tile is non-empty.
                        ++ [ Loop.LoopNonEmpty ]
                  
                  -- TODO: can be more optimal, maybe don't need to retrieve it the first time                  
                  prevMustFinish <- instr' $ LoadBool NonVolatile mustFinish    -- is false first tile
                  prevHasFinished <- instr' $ LoadBool NonVolatile hasFinished  -- is true first tile

                  A.when (return $ A.liftBool isFirstTileLoop) $ do
                    ptBefore tileLoop envs'''' -- The pre-tile loop
                    Loop.loopWith ann (isDescending direction) lower upper $ \isFirst idx -> do
                      localIdx <- A.sub numType idx lower
                      let envs''''' = envs''''{
                          envsLoopDepth = 1,
                          envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs''',
                          envsIsFirst = isFirst,
                          envsTileLocalIndex = localIdx
                        }
                      genSequential envs''''' loops'' $ ptIn tileLoop -- The tile loop

                    -- Currently not truly interleaving, since the reduction only shares at the start of the next phase? This couldbe solved by storing the reduction in this phase
                    -- Perform the previous lookback here IF prevHasFinished is false
                    void $ A.ifThenElse' (TupRunit, OP_Bool prevHasFinished)
                      (do
                        lookbackFinished <- ptAfter tileLoop envs''''
                        _ <- instr' $ Store NonVolatile hasFinished $ op BoolPrimType $ OP_Bool lookbackFinished
                        return OP_Unit
                      )
                      (do
                        prevIndexVal <- tupleLoad (TupRsingle scalarTypeInt) prevIndex
                        -- TODO: duplicate code
                        let prevEnv = envs''''{
                            -- envsIsFirst = A.liftBool False,
                            envsTileIndex = prevIndexVal
                          }
                        -- It needs to succeed this time, so set mustFinish to true
                        _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool True) -- Move this to prevIndex set moment
                        _ <- ptAfter tileLoop prevEnv -- disregard outcome, since it is always true
                        
                        _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool False)
                        lookbackFinished <- ptAfter tileLoop envs''''
                        _ <- instr' $ Store NonVolatile hasFinished $ op BoolPrimType $ OP_Bool lookbackFinished

                        _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool True) -- Needs to be set to true again so we actually perform our previous scan-phase

                        return OP_Unit
                      )
                  
                  -- TODO: maybe put this in where?
                  isNotFirstTileLoop <- A.lnot $ A.liftBool isFirstTileLoop
                  -- Perform previous tiles if mustFinish is true, NOTE this only works for non-fused scans currently
                  A.when (A.land isNotFirstTileLoop (OP_Bool prevMustFinish)) $ do
                    prevIndexVal <- tupleLoad (TupRsingle scalarTypeInt) prevIndex
                      -- TODO: duplicate code
                    let prevEnv = envs''''{
                        -- envsIsFirst = A.liftBool False,
                        envsTileIndex = prevIndexVal
                      }

                    -- Basically change lower and upper to be good and you are good
                    prevTileIdxAbsolute <- -- TODO: duplicate code
                      if isDescending direction then do
                        i <- A.sub numType (OP_Int tileCount') prevIndexVal
                        A.sub numType i (A.liftInt 1)
                      else
                        return prevIndexVal
                    prevLower <- A.mul numType prevTileIdxAbsolute (A.liftInt tileSize)
                    prevUpper' <- A.add numType prevLower (A.liftInt tileSize)
                    prevUpper <- A.min singleType prevUpper' size
                    
                    ptBefore tileLoop prevEnv -- The pre-tile loop
                    Loop.loopWith ann (isDescending direction) prevLower prevUpper $ \isFirst idx -> do -- TODO: look here for what index it is
                      localIdx <- A.sub numType idx prevLower

                      let envs''''' = prevEnv{
                          envsLoopDepth = 1,
                          envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs''',
                          envsIsFirst = isFirst,
                          envsTileLocalIndex = localIdx
                        }
                      genSequential envs''''' loops'' $ ptIn tileLoop -- The tile loop
                    _ <- ptAfter tileLoop prevEnv

                    return ()

                  -- Perform other steps if lookback was successful, and if hasFinished is true
                  A.when (return isNotFirstTileLoop) $ do
                    -- obviously should be an ifthenelse instead
                    A.when (return $ OP_Bool prevHasFinished) $ do
                      ptBefore tileLoop envs'''' -- The pre-tile loop
                      Loop.loopWith ann (isDescending direction) lower upper $ \isFirst idx -> do
                        localIdx <- A.sub numType idx lower
                        let envs''''' = envs''''{
                            envsLoopDepth = 1,
                            envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs''',
                            envsIsFirst = isFirst,
                            envsTileLocalIndex = localIdx
                          }
                        genSequential envs''''' loops'' $ ptIn tileLoop -- The tile loop
                      _ <- ptAfter tileLoop envs''''
                      return ()
  
                -- LAST HERE IN TL2, go one more iteration
                -- set mustFinish to false now, since it has finished
                
                prevHasFinished <- instr' $ LoadBool NonVolatile hasFinished  -- is true first tile
                A.unless (return $ OP_Bool prevHasFinished) $ do -- THE PREV INDEX SHOULD ONLY CHANGE AFTER THE TILE LOOP? YES THIS IS CORRECT
                  tupleStore (TupRsingle scalarTypeInt) prevIndex (OP_Int tileIdx)
                  return ()
                _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool False)               
                return OP_Unit
              )

            return ()
            
          
          -- perform final loop of the function
          prevHasFinished <- instr' $ LoadBool NonVolatile hasFinished  -- is true first tile

          -- TODO: optimize this loop
          A.unless (return $ OP_Bool prevHasFinished) $ do
            -- set mustFinish to true?
            _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool True)
            prevIndexVal <- tupleLoad (TupRsingle scalarTypeInt) prevIndex
            let envs'''' = envs'''{
                envsTileIndex = prevIndexVal
              }


            -- TODO: change these upper and lower to not fully calculate it again at this point for seemingly no reason :)
            tileIdxAbsolute <-
                -- For a scanr, convert low-to-high indices to high-to-low indices:
                -- The first block (with tileIdx 0) should now correspond with the last
                -- values of the array. We implement that by reversing the tile indices here.
                if isDescending direction then do
                  i <- A.sub numType (OP_Int tileCount') prevIndexVal
                  A.sub numType i (A.liftInt 1)
                else
                  return prevIndexVal
            lower <- A.mul numType tileIdxAbsolute (A.liftInt tileSize)
            upper' <- A.add numType lower (A.liftInt tileSize)
            upper <- A.min singleType upper' size

            forM_ ((True, ptFirstLoop tileLoops) : map (False, ) (ptOtherLoops tileLoops)) $ \(isFirstTileLoop, tileLoop) -> do
              -- All nested loops are placed in the first tile loop by parCodeGens
              let loops'' = if isFirstTileLoop then loops' else []
              let ann =
                    -- Only do loop peeling if requested and when there are no nested loops.
                    -- Peeling over nested loops causes a lot of code duplication,
                    -- and is probably not worth it.
                    [ Loop.LoopPeel | ptPeel tileLoop && null loops'' ]
                    -- LLVM cannot vectorize loops containing scans (yet).
                    -- The first tile loop only does a reduction, others will perform a scan.
                    -- Loops containing permute (not permuteUnique) can
                    -- also not be vectorized.
                    -- Reduction cannot always be vectorized. This might in particular fail
                    -- on reductions of multiple values (tuples/pairs). For now, we thus do
                    -- not request vectorization, until we can reliably know whether LLVM can
                    -- vectorize something, or generate our code in a form that LLVM can
                    -- definitely vectorize.
                    ++ [ Loop.LoopInterleave ] -- Loop.LoopVectorize
                    -- We can use LoopNonEmpty since we
                    -- know that each tile is non-empty.
                    ++ [ Loop.LoopNonEmpty ]

              A.when (return $ A.liftBool isFirstTileLoop) $ do
                _ <- ptAfter tileLoop envs''''
                return ()
              A.unless (return $ A.liftBool isFirstTileLoop) $ do
                ptBefore tileLoop envs'''' -- The pre-tile loop
                Loop.loopWith ann (isDescending direction) lower upper $ \isFirst idx -> do
                  localIdx <- A.sub numType idx lower
                  let envs''''' = envs''''{
                      envsLoopDepth = 1,
                      envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs''',
                      envsIsFirst = isFirst,
                      envsTileLocalIndex = localIdx
                    }
                  genSequential envs''''' loops'' $ ptIn tileLoop -- The tile loop
                _ <- ptAfter tileLoop envs''''
                return ()

          ptExit tileLoops envs''

          retval_ $ scalar (scalarType @Word8) 0
          -- Return the size of kernel memory
          pure $ fst $ primSizeAlignment memoryTp
    else do
      -- Parallelise over all independent dimensions
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS

      -- If we parallelize over all dimensions, choose a large tile size.
      -- The work per iteration is probably very small.
      -- If we do not parallelize over all dimensions, choose a tile size of 1.
      -- The work per iteration is probably large enough.
      let tileSize = if parallelDepth == rank shr then chunkSize parallelShr else chunkSizeOne parallelShr
      let parSizes = parallelIterSize parallelShr loops

      setBlock initBlock
      do
        tileCount <- chunkCount parallelShr parSizes (A.lift (shapeType parallelShr) tileSize)
        tileCount' <- shapeSize parallelShr tileCount
        -- We are not using kernel memory, so no need to initialize it.

        OP_Bool isSmall <- A.lt singleType tileCount' $ A.liftInt 2
        value <- instr' $ Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
        retval_ value

      setBlock finishBlock
      -- Nothing has to be done in the finish function for this kernel.
      retval_ $ scalar (scalarType @Word8) 0

      setBlock workBlock
      let ann =
            if parallelDepth /= rank shr then []
            else {- if hasPermute then -} [Loop.LoopInterleave]
            -- else [Loop.LoopVectorize]
      workassistChunked ann parallelShr workassistIndex workassistFirstIndex tileSize parSizes $ \idx -> do
        let envs' = envs{
            envsLoopDepth = parallelDepth,
            envsIdx =
              foldr (\(o, i) -> Env.partialUpdate o i) (envsIdx envs)
              $ zip (shapeOperandsToList parallelShr idx) (map (\(i, _, _) -> i) loops),
            -- Independent operations should not depend on envsIsFirst.
            envsIsFirst = OP_Bool $ boolean False,
            envsDescending = False
          }
        genSequential envs' (drop parallelDepth loops) $ opCodeGens opCodeGen flatOps

      pure 0
  where
    (argTp, extractEnv, workassistIndex, workassistFirstIndex, kernelMem', gamma) = bindHeaderEnv env

    isDescending :: LoopDirection Int -> Bool
    isDescending LoopDescending = True
    isDescending _ = False

linkage :: Maybe LP.Linkage
linkage = Just LP.DLLExport

opCodeGen :: FlatOp NativeOp env idxEnv -> (LoopDepth, OpCodeGen Native NativeOp env idxEnv)
opCodeGen flatOp@(FlatOp op args idxArgs) = case op of
  NGenerate -> defaultCodeGenGenerate args idxArgs
  NMap -> defaultCodeGenMap args idxArgs
  NBackpermute -> defaultCodeGenBackpermute args idxArgs
  NPermute
    | (_ :>: output :>: _ :>: _) <- args ->
      defaultCodeGenPermute (\envs j _ -> atomically envs output $ OP_Int j) args idxArgs
  NPermute' -> defaultCodeGenPermuteUnique args idxArgs
  NFold -> defaultCodeGenFold flatOp args idxArgs
  NFold1 -> defaultCodeGenFold1 flatOp args idxArgs
  NScan1 dir -> defaultCodeGenScan1 dir flatOp args idxArgs
  NScan' dir -> defaultCodeGenScan' dir flatOp args idxArgs
  NScan dir -> defaultCodeGenScan dir flatOp args idxArgs

-- Parallel code generation for one-dimensional collective operations (folds and scans).
-- Other operations, either OpCodeGenSingle or nested deeper, are handled in opCodeGen
parCodeGen :: Bool -> Operand (Ptr Bool) -> FlatOp NativeOp env idxEnv -> Maybe (Exists (ParLoopCodeGen Native env idxEnv))
parCodeGen descending _ (FlatOp NFold
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun (Just seed) input output inputIdx outputIdx
parCodeGen descending _ (FlatOp NFold1
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun Nothing input output inputIdx outputIdx
parCodeGen descending mustFinish (FlatOp (NScan1 _)
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenScanLookback descending mustFinish IsScan fun Nothing input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result) -- make an if else on mustFinish, whether to use outputIdx, OR generate one ourselves using envsTileIndex
    (\_ _ -> return ())
  where -- multiple rowIdx's
    rowIdx = case inputIdx of
        TupRpair i _ -> i
        _ -> internalError "Shape impossible"
parCodeGen descending mustFinish (FlatOp (NScan' _)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx _ foldOutputIdx :>: _))
  = Just $ parCodeGenScanLookback descending mustFinish IsScan fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
    (\envs result -> writeArray' envs foldOutput foldOutputIdx result)
parCodeGen descending mustFinish (FlatOp (NScan dir)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: _ :>: _))
  = case dir of
      LeftToRight -> Just $ parCodeGenScanLookback descending mustFinish IsScan fun (Just seed) input inputIdx -- Change this for testcase
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\_ _ -> return ())
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
      RightToLeft -> Just $ parCodeGenScanLookback descending mustFinish IsScan fun (Just seed) input inputIdx
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\_ _ -> return ())
  where
    ArgArray _ _ inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
parCodeGen _ _ _  = Nothing

parCodeGenFold
  :: Bool
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e)
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenFold descending fun Nothing input output inputIdx outputIdx
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenFold descending fun (Just $ mkConstant tp identity) input output inputIdx outputIdx
  where
    ArgArray _ (ArrayR _ tp) _ _ = output
-- Specialized version for commutative folds with identity
parCodeGenFold descending fun seed input output inputIdx outputIdx
  | isCommutative fun
  , Just s <- seed
  , Just i <- identity
  = parCodeGenFoldCommutative descending fun s i input output inputIdx outputIdx
  | otherwise
  = parCodeGenScan descending IsFold fun seed input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
  where
    ArgArray _ (ArrayR _ tp) _ _ = output
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing

parCodeGenFoldCommutative
  :: Bool
  -> Fun env (e -> e -> e)
  -> Exp env e
  -> Exp env e
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenFoldCommutative _ fun seed identity input output inputIdx outputIdx = Exists $ ParLoopCodeGen
  False
  -- In kernel memory, store a lock (Word8) and the
  -- reduced value so far. The lock must be acquired to read or update the total value.
  -- Value 0 means unlocked, 1 is locked.
  (mapTupR ScalarPrimType memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeWord8 0) -- unlocked
        value <- llvmOfExp (compileArrayInstrEnvs envs) seed
        tupleStore tp valuePtrs value
  )
  -- Initialize a thread
  (\_ envs -> do
    accumVar <- tupleAlloca tp
    value <- llvmOfExp (compileArrayInstrEnvs envs) identity
    tupleStore tp accumVar value
    return accumVar
  )
  -- Code before the tile loop
  (\_ _ _ _ -> return ())
  -- Code within the tile loop
  (\_ accumVar _ envs -> do
    x <- readArray' envs input inputIdx
    accum <- tupleLoad tp accumVar
    new <-
      if envsDescending envs then
        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
      else
        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
    tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\_ _ _ _ -> return (boolean True)) -- returning true should be fine I think
  -- Code at the end of a thread
  (\accumVar ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle lock) valuePtrs -> do
        -- TODO: Use atomic compare-and-swap or read-modify-write
        -- to update the value in kernel memory lock-free,
        -- instead of taking a lock here.
        _ <- Loop.while [] TupRunit
          (\_ -> do
            -- While the lock is taken
            old <- instr $ AtomicRMW numType NonVolatile Exchange lock (scalar scalarTypeWord8 1) (CrossThread, Acquire)
            A.neq singleType old (A.liftWord8 0)
          )
          (\_ -> return OP_Unit)
          OP_Unit

        local <- tupleLoad tp accumVar

        old <- tupleLoad tp valuePtrs
        new <-
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local old
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) old local
        tupleStore tp valuePtrs new

        -- Release the lock
        _ <- instr' $ Fence (CrossThread, Release)
        _ <- instr' $ Store Volatile lock (scalar scalarTypeWord8 0)
        return ()
  )
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair _ valuePtrs -> do
        value <- tupleLoad tp valuePtrs
        writeArray' envs output outputIdx value
  )
  Nothing
  where
    memoryTp = TupRsingle scalarTypeWord8 `TupRpair` tp
    ArgArray _ (ArrayR _ tp) _ _ = input

data FoldOrScan = IsFold | IsScan deriving Eq


parCodeGenScanLookback
  :: forall e sh env idxEnv.
     Bool -- Whether the loop is descending
  -- Whether this is a fold. Folds use similar code generation as scans, hence
  -- it is handled here. Commutative folds are handled separately.
  -> Operand (Ptr Bool) -- Whether this loop must finish, or can return early (when interleaving half-sized tiles)
  -> FoldOrScan
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed
  -> Arg env (In (sh, Int) e)
  -> ExpVars idxEnv (sh, Int)
  -- Code after evaluating the seed
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code in a tile loop, before the combination (for exclusive scans)
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code in a tile loop, after the combination (for inclusive scans)
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenScanLookback descending mustFinish foldOrScan fun Nothing input index codeSeed codePre codePost codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScanLookback descending mustFinish foldOrScan fun (Just $ mkConstant tp identity) input index codeSeed codePre codePost codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input -- maak het een struct zodat het de waarde van iets is of  PrimTypetuple
parCodeGenScanLookback descending mustFinish foldOrScan fun seed input index codeSeed codePre codePost codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  memoryTp -- MemoryTp is now already primType 
  -- Initialize kernel memory, use only the first value for now
  (\ptr envs -> do
    ptrs <- tuplePtrs' memoryTp ptr
    case ptrs of
      TupRsingle tileArray -> do
          let tileCount = envsTileCount envs
          loopAmount <- A.min singleType (A.liftInt (fromIntegral arraySize)) (OP_Int tileCount)
          imapFromStepTo [Loop.LoopNonEmpty] (A.liftInt 0) (A.liftInt 1) loopAmount (\(OP_Int idx) -> do
            _ <- tupleStoreArray (TupRsingle scalarTypeWord8) NonVolatile tileArray idx tileFlagidx unfinishedFlag
            return ()
            )
          case seed of
            Nothing -> return ()
            Just s -> do
              value <- llvmOfExp (compileArrayInstrEnvs envs) s
              codeSeed envs value
              tupleStoreArray tp NonVolatile tileArray (scalar scalarTypeInt 0) prefixidx value)

  -- Initialize a thread
  (\_ _ -> do
    tupleAlloca threadMemTp
  )
  -- Code before the tile loop
  (\singleThreaded threadMem ptr envs -> do
    case threadMem of
      TupRpair accumVar _ -> do
        -- Initialize the prevIndex, TODO change this for 
        if singleThreaded then do
          -- In the single threaded mode, we directly do a scan over this tile,
          -- instead of the reduce, lookback and scan phases.
          ptrs <- tuplePtrs' memoryTp ptr
          case ptrs of
            TupRsingle tileArray -> do -- Memory access
              prevIndex <- indexMin1 (envsTileIndex envs)
              safePrevIndex <- A.max singleType (A.liftInt 0) prevIndex --TODO: waarom is hier safePrevIndex nodig?
              prefix <- tupleLoadArray tp NonVolatile tileArray (opsToOpInt safePrevIndex) prefixidx
              tupleStore tp accumVar prefix
            --   -- Note: on the first tile, we read an undefined value if there is no
            --   -- seed. This is fine, as we don't use this value in the tile loop.
        else do
          case identity of
            Nothing -> return ()
            Just identity' -> do
              value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
              tupleStore tp accumVar value
          -- Should we be doing the prevAccumvar check here?
      TupRsingle _ -> internalError "threadMemory impossible from before the tileLoop"

  )
  -- Code within the tile loop
  (\singleThreaded threadMem ptr envs -> do
    case threadMem of
      TupRpair accumVar _ -> do

        if singleThreaded then do
          -- Single threaded mode. We directly perform a scan here.
          x <- readArray' envs input index
          if isJust seed then do
            accum <- tupleLoad tp accumVar
            codePre envs accum
            new <- if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
            codePost envs new -- REMOVE: basically writes to the array
            tupleStore tp accumVar new
          else do
            isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
            new <- A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
              ( do
                return x
              )
              ( do
                accum <- tupleLoad tp accumVar
                codePre envs accum
                if envsDescending envs then
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
                else
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
              )
            codePost envs new
            tupleStore tp accumVar new
        else do
          -- Parallel mode.
          -- Execute the reduce-phase of a parallel chained scan here.
          x <- readArray' envs input index
          new <-
            if isJust identity then do
              accum <- tupleLoad tp accumVar
              if envsDescending envs then
                app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
              else
                app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
            else
              A.ifThenElse' (tp, envsIsFirst envs)
                ( do
                  return x
                )
                ( do
                  accum <- tupleLoad tp accumVar
                  if envsDescending envs then
                    app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
                  else
                    app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
                )

          tupleStore tp accumVar new

          ptrs <- tuplePtrs' memoryTp ptr
          
          case ptrs of
            TupRsingle tileArray -> do
              tupleStoreArray tp NonVolatile tileArray (singleEnvIndex envs) reductionidx new

      TupRsingle _ -> internalError "threadMemory impossible from reduce phase"
  )
  -- Code after the tile loop
  (\singleThreaded threadMem ptr envs -> do
    case threadMem of
      TupRpair accumVar prevAccumVar -> do
        
        ptrs <- tuplePtrs' memoryTp ptr
        local <- tupleLoad tp accumVar
        
        case ptrs of
          TupRsingle tileArray -> do
            -- Should only go once in singleThreaded mode regardless of mustFinish
            if singleThreaded then do
                tupleStoreArray tp NonVolatile tileArray (singleEnvIndex envs) prefixidx local
                _ <- instr' $ Fence (CrossThread, Release)
                tupleStoreArray (TupRsingle scalarTypeWord8) Volatile tileArray (singleEnvIndex envs) tileFlagidx prefixFlag -- Set the flag to 2 (prefix available)
                
                return $ boolean True
              else do
                mustFinishVal <- instr' $ LoadBool NonVolatile mustFinish

                -- Release the reduction of this tile, since tileLoop has finished (is currently released twice, but shouldn't affect behaviour)
                _ <- instr' $ Fence (CrossThread, Release)
                tupleStoreArray (TupRsingle scalarTypeWord8) NonVolatile tileArray (singleEnvIndex envs) tileFlagidx reductionFlag


                -- Store the local result in the tile array
                -- TODO: for variant this should check should come in case 2 instead
                A.when (return $ OP_Bool mustFinishVal) (do -- scalarTypeWord8 functions as a bool once again :)
                  -- Local can be different than tileLoop local, therefore we get it from kernel memory
                  
                  prevLocal <- tupleLoadArray tp NonVolatile tileArray (singleEnvIndex envs) reductionidx

                  prevIndex <- indexMin1 (envsTileIndex envs)
                  maybeStart <- case identity of
                    Just identity' -> do
                      value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
                      return (OP_Pair value word8True)
                    Nothing -> return (OP_Pair prevLocal word8False) -- local is used as a dummy value which is never used
                  let loopVartp = TupRpair 
                                    (TupRpair (TupRsingle scalarTypeWord8) (TupRsingle scalarTypeInt)) -- (flag, index)
                                    (TupRpair tp (TupRsingle scalarTypeWord8)) -- (reduction, (hasValue, isPrevBlock)) scalarTypeWord8 in place of a boolean, 0 for stop looping, 1 for keep looping


                  result <- Loop.while [Loop.LoopNonEmpty] loopVartp
                    (\loopVar -> do
                      let OP_Pair (OP_Pair keepLooping _) _ = loopVar

                      A.eq singleType keepLooping word8True -- If keepLooping is 1 (true), keep looping
                    )
                    (\loopVar -> do
                      case loopVar of
                        OP_Pair (OP_Pair _ curIndex) (OP_Pair curReduction hasValue) -> do

                          curFlag <- tupleLoadArray (TupRsingle scalarTypeWord8) Volatile tileArray (opsToOpInt curIndex) tileFlagidx
                          _ <- instr' $ Fence (CrossThread, Acquire)


                          A.ifThenElse (loopVartp, A.eq singleType curFlag prefixFlag)
                            (do -- flag is 2, Load prefix, and add it to loopVar before returning it
                              prefix <- tupleLoadArray tp NonVolatile tileArray (opsToOpInt curIndex) prefixidx

                              newReduction <- A.ifThenElse (tp, A.eq singleType hasValue word8True)
                                (
                                  if envsDescending envs then
                                    app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) curReduction prefix
                                  else
                                    app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix curReduction
                                )
                                (return prefix)


                              -- Storing in kernel memory since accumVar is from different tileLoop
                              -- tupleStoreArray tp NonVolatile tileArray (opsToOpInt curIndex) reductionidx newReduction
                              -- tupleStore tp accumVar newReduction

                              return $ OP_Pair (OP_Pair word8False curIndex) (OP_Pair newReduction word8True)

                            )
                            (A.ifThenElse (loopVartp, A.eq singleType curFlag reductionFlag)
                              (do -- flag is 1, Load reduction, and add it to loopVar before returning it                          
                                  reduction <- tupleLoadArray tp NonVolatile tileArray (opsToOpInt curIndex) reductionidx

                                  newReduction <- A.ifThenElse (tp, A.eq singleType hasValue word8True)
                                    (
                                      if envsDescending envs then
                                        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) curReduction reduction
                                      else
                                        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) reduction curReduction
                                    )
                                    (return reduction)

                                  newIndex <- indexMin1 curIndex

                                  return $ OP_Pair (OP_Pair word8True newIndex) (OP_Pair newReduction word8True) -- ((flag, index) (accumReduction, (hasValue, isPrevBlock)))
                              )
                              (do
                                return loopVar)
                            )
                    )
                    ( OP_Pair (OP_Pair word8True prevIndex) maybeStart
                    )
                  let OP_Pair _ (OP_Pair prefix _) = result
                  -- Apply the prefix to our local reduction
                  incl_prefix <- ( if envsDescending envs then
                          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prevLocal prefix
                        else
                          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix prevLocal
                    )

                  tupleStoreArray tp NonVolatile tileArray (singleEnvIndex envs) prefixidx incl_prefix
                  _ <- instr' $ Fence (CrossThread, Release)
                  tupleStoreArray (TupRsingle scalarTypeWord8) Volatile tileArray (singleEnvIndex envs) tileFlagidx prefixFlag -- Set the flag to 2 (prefix available)
                  
                  -- TODO: For variant, store in prevVar instead of accumVar iff mustFinish, i might already be in mustFinishVal here, so this check is unnecessary
                  tupleStore tp prevAccumVar prefix

                    -- writing this seems double, but will be needed for disambiguation of the variant later
                  -- _ <- instr' $ Store NonVolatile mustFinish $ op BoolPrimType (A.liftBool False)   

                  -- return localResult
                  
                  )
                return mustFinishVal
      TupRsingle _ -> internalError "threadMemory impossible from ptAfter tileLoop"
  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    -- hier gebeurt ook iets wackys
    ptrs <- tuplePtrs' memoryTp ptr
    case ptrs of
      TupRsingle tileArray -> do
        lastIndex <- indexMin1 $ OP_Int (envsTileCount envs)
        safeLastIndex <- A.max singleType (A.liftInt 0) lastIndex

        value <- tupleLoadArray tp NonVolatile tileArray (opsToOpInt safeLastIndex) prefixidx

        codeEnd envs value
  )
  -- In the next tile loop, we prefer loop peeling iff there is no seed.
  -- In the first iteration, the first tile loop will then start without a prefix value,
  -- and we thus should do loop peeling there.
  -- Not executed when this tile is executed in the sequential mode.
  (if foldOrScan == IsFold then Nothing else
    Just (isNothing seed, \threadMem _ envs -> do
      case threadMem of
        TupRpair accumVar prevAccumVar -> do
          -- We use the prevAccumvar generally, but if no mustFinish, we can use the regular since no half-sized block in storage 
          -- First time, load accumVar from kernel memory
          A.when (return $ envsIsFirst envs) (do
            mustFinishVal <- instr' $ LoadBool NonVolatile mustFinish

            A.unless (return $ OP_Bool mustFinishVal) $ do
              excl_prefix <- tupleLoad tp accumVar
              tupleStore tp prevAccumVar excl_prefix
            )

          x <- readArray' envs input index
          if isJust seed then do
            accum <- tupleLoad tp prevAccumVar
            codePre envs accum
            new <- if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
            codePost envs new
            tupleStore tp prevAccumVar new
          else do
            isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
            new <- A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
              ( do
                return x
              )
              ( do
                accum <- tupleLoad tp prevAccumVar
                codePre envs accum
                if envsDescending envs then
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
                else
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
              )
            codePost envs new
            tupleStore tp prevAccumVar new
        TupRsingle _ -> internalError "threadMemory impossible from scan phase"
    )
  )
  where
    memoryTp = TupRsingle tileArray
    -- tileArray = 
    ArgArray _ (ArrayR _ tp) _ _ = input

    -- flag + reduction + prefix 
    -- Having the type ruins it?

    tileTP :: PrimType (Struct ((Word8, e), e))
    tileTP = StructPrimType False $
      TupRsingle (ScalarPrimType scalarTypeWord8) `TupRpair`
      mapTupR ScalarPrimType tp `TupRpair`
      mapTupR ScalarPrimType tp
    tileArray :: PrimType (SizedArray  (Struct ((Word8, e), e)))
    tileArray = ArrayPrimType arraySize tileTP -- No clue how many tiles I need, should look into this, prob make this a variable so I can have minimum for this and tilecount in filling of array
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing
    threadMemTp :: TupR ScalarType (e, e) -- Accumvar, prevAccumVar
    threadMemTp = TupRpair tp tp
    tileFlagidx = tupleLeft (tupleLeft TupleIdxSelf)
    reductionidx = tupleRight (tupleLeft TupleIdxSelf)
    prefixidx = tupleRight TupleIdxSelf
    singleEnvIndex envs = case envsTileIndex envs of
      OP_Int idx -> idx
    indexMin1 idx = A.sub numType idx (A.liftInt 1)
    opsToOpInt (OP_Int i) = i
    arraySize :: Word64 -- Temporary array size, should be circular eventually
    arraySize = 32768
    unfinishedFlag :: Operands Word8
    unfinishedFlag = A.liftWord8 0
    reductionFlag :: Operands Word8
    reductionFlag = A.liftWord8 1
    prefixFlag :: Operands Word8
    prefixFlag = A.liftWord8 2
    word8True :: Operands Word8 -- These should be booleans eventually, but for now word8 works
    word8True = A.liftWord8 1
    word8False :: Operands Word8
    word8False = A.liftWord8 0
    unavailableIdx :: Operands Int
    unavailableIdx = A.liftInt (-1)


parCodeGenScan
  :: Bool -- Whether the loop is descending
  -- Whether this is a fold. Folds use similar code generation as scans, hence
  -- it is handled here. Commutative folds are handled separately.
  -> FoldOrScan
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed
  -> Arg env (In (sh, Int) e)
  -> ExpVars idxEnv (sh, Int)
  -- Code after evaluating the seed
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code in a tile loop, before the combination (for exclusive scans)
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code in a tile loop, after the combination (for inclusive scans)
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenScan descending foldOrScan fun Nothing input index codeSeed codePre codePost codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScan descending foldOrScan fun (Just $ mkConstant tp identity) input index codeSeed codePre codePost codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
parCodeGenScan descending foldOrScan fun seed input index codeSeed codePre codePost codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  (mapTupR ScalarPrimType memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeInt 0)
        case seed of
          Nothing -> return ()
          Just s -> do
            value <- llvmOfExp (compileArrayInstrEnvs envs) s
            codeSeed envs value
            tupleStore tp valuePtrs value
  )
  -- Initialize a thread
  (\_ _ -> tupleAlloca tp)
  -- Code before the tile loop
  (\singleThreaded accumVar ptr envs ->
    if singleThreaded then do
      -- In the single threaded mode, we directly do a scan over this tile,
      -- instead of the reduce, lookback and scan phases.
      ptrs <- tuplePtrs memoryTp ptr
      case ptrs of
        TupRsingle _ -> internalError "Pair impossible"
        TupRpair _ valuePtrs -> do
          prefix <- tupleLoad tp valuePtrs
          tupleStore tp accumVar prefix
          -- Note: on the first tile, we read an undefined value if there is no
          -- seed. This is fine, as we don't use this value in the tile loop.
    else
      case identity of
        Nothing -> return ()
        Just identity' -> do
          value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
          tupleStore tp accumVar value
  )
  -- Code within the tile loop
  (\singleThreaded accumVar _ envs ->
    if singleThreaded then do
      -- Single threaded mode. We directly perform a scan here.
      x <- readArray' envs input index
      if isJust seed then do
        accum <- tupleLoad tp accumVar
        codePre envs accum
        new <- if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        codePost envs new
        tupleStore tp accumVar new
      else do
        isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
        new <- A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
          ( do
            return x
          )
          ( do
            accum <- tupleLoad tp accumVar
            codePre envs accum
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
          )
        codePost envs new
        tupleStore tp accumVar new
    else do
      -- Parallel mode.
      -- Execute the reduce-phase of a parallel chained scan here.
      x <- readArray' envs input index
      new <-
        if isJust identity then do
          accum <- tupleLoad tp accumVar
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        else
          A.ifThenElse' (tp, envsIsFirst envs)
            ( do
              return x
            )
            ( do
              accum <- tupleLoad tp accumVar
              if envsDescending envs then
                app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
              else
                app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
            )
      tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\singleThreaded accumVar ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle idxPtr) valuePtrs -> do
        if singleThreaded then
          -- It is our turn since we are in the sequential mode,
          -- no need to wait
          return ()
        else do
          _ <- Loop.while [] TupRunit
            (\_ -> do
              idx <- instr $ Load scalarTypeInt Volatile idxPtr
              A.neq singleType idx (envsTileIndex envs)
            )
            (\_ -> return OP_Unit)
            OP_Unit
          _ <- instr' $ Fence (CrossThread, Acquire)
          return ()

        local <- tupleLoad tp accumVar

        new <-
          if singleThreaded then
            -- In the single threaded mode, 'local' is already the prefix,
            -- as this loop starts with the prefix value of the previous
            -- thread. We can directly write that to kernel memory.
            return local
          else if isNothing seed then
            -- If there is no seed, then write the output directly in the first tiles.
            -- The other tiles must combine their result with the given operator.
            -- Note that the first tile should typically be handled in the sequential mode,
            -- but this sequential mode is not always generated:
            -- A non-commutative fold is handled as a scan without the sequential mode.
            -- Furthermore we could decide to skip the sequential mode if it leads to
            -- a lot of code duplication (but we don't do that yet).s
            A.ifThenElse (tp, A.eq singleType (envsTileIndex envs) (A.liftInt 0))
              (do
                return local
              )
              (do
                prefix <- tupleLoad tp valuePtrs
                tupleStore tp accumVar prefix
                if envsDescending envs then
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
                else
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
              )
          -- If there is a seed, then all tile will combine their local result with
          -- the already available value.
          else do
            -- If there is no seed, then write the output directly in the first tiles.
            -- The other tiles must combine their result with the given operator.

            prefix <- tupleLoad tp valuePtrs
            tupleStore tp accumVar prefix
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
        tupleStore tp valuePtrs new

        _ <- instr' $ Fence (CrossThread, Release)
        OP_Int nextIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
        _ <- instr' $ Store Volatile idxPtr nextIdx
        return (boolean True) -- Boolean is not used
  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair _ valuePtrs -> do
        value <- tupleLoad tp valuePtrs
        codeEnd envs value
  )
  -- In the next tile loop, we prefer loop peeling iff there is no seed.
  -- In the first iteration, the first tile loop will then start without a prefix value,
  -- and we thus should do loop peeling there.
  -- Not executed when this tile is executed in the sequential mode.
  (if foldOrScan == IsFold then Nothing else
    Just (isNothing seed, \accumVar _ envs -> do
      x <- readArray' envs input index
      if isJust seed then do
        accum <- tupleLoad tp accumVar
        codePre envs accum
        new <- if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        codePost envs new
        tupleStore tp accumVar new
      else do
        isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
        new <- A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
          ( do
            return x
          )
          ( do
            accum <- tupleLoad tp accumVar
            codePre envs accum
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
          )
        codePost envs new
        tupleStore tp accumVar new
    )
  )
  where
    memoryTp = TupRsingle scalarTypeInt `TupRpair` tp
    ArgArray _ (ArrayR _ tp) _ _ = input
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing

-- Checks if the cluster has a permute.
hasNPermute :: FlatCluster NativeOp env -> Bool
hasNPermute (FlatCluster _ _ _ _ _ _ flatOps) = go flatOps
  where
    go :: FlatOps NativeOp env idxEnv -> Bool
    go FlatOpsNil = False
    go (FlatOpsBind _ _ _ ops) = go ops
    go (FlatOpsOp (FlatOp NPermute _ _) _) = True
    go (FlatOpsOp (FlatOp NPermute' _ _) _) = True
    go (FlatOpsOp _ ops) = go ops
