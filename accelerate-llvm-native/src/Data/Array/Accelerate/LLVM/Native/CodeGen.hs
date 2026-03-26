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
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction as LLVM
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists))
import Control.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Data.Array.Accelerate.LLVM.Internal.LLVMPretty as LP
import Data.Array.Accelerate.LLVM.CodeGen.Loop (imapFromStepTo)

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

      -- Parallelise over first dimension using parallel folds or scans
      case parCodeGens (parCodeGen $ isDescending direction) 0 $ opCodeGens opCodeGen flatOps of
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
                  1024 * 2 -- only for debugging
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
            value <- instr' $ LLVM.Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
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
          envs'' <-
            -- Binding locals on dimension 0. This is not needed for fused away
            -- arrays, but we use the same mechanism to handle unused outputs.
            -- This is particularly important for scanl, as we cannot fuse over
            -- the output of a scanl (opposed to scanl1 and scanl'). In
            -- SetOpIndices we do not set the index of the output, and that
            -- causes it to be placed on dimension 0. Hence we need to bind it
            -- here.
            bindLocals 0 envs' >>=
            bindLocalsInTile (\_ -> not $ null $ ptOtherLoops tileLoops) 1 tileSize
          workassistLoop workassistIndex workassistFirstIndex tileCount $ \seqMode tileIdx' -> do
            tileIdx <- instr' $ BitCast scalarType tileIdx'
            (_, lower, upper, _) <- tileRange (isDescending direction) (op TypeInt size) (integral TypeInt tileSize) tileCount' tileIdx

            -- If there is only a single tile loop (i.e. no parallel scans),
            -- then we don't generate code for a single-threaded mode:
            -- the default mode already is as fast as a single-threaded mode.
            let seqMode' = if null (ptOtherLoops tileLoops) then boolean False else seqMode

            let envs''' = envs''{
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
                      [ Loop.LoopPeel | cpuLoopPeel (ptAnalysis tileLoop) && null loops' ]
                      -- We can use LoopNonEmpty since we
                      -- know that each tile is non-empty.
                      -- We cannot vectorize this loop (yet), as LLVM cannot vectorize loops
                      -- containing scans. We should either wait until LLVM supports this,
                      -- or vectorize loops (partially) ourselves.
                      -- As an alternative to vectorization, we ask LLVM to interleave the loop.
                      ++ [ Loop.LoopNonEmpty, Loop.LoopInterleave ]

                ptBefore tileLoop envs'''
                Loop.loopWith ann (isDescending direction) (OP_Int lower) (OP_Int upper) $ \isFirst idx -> do
                  localIdx <- A.sub numType idx (OP_Int lower)
                  let envs'''' = envs'''{
                      envsLoopDepth = 1,
                      envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs''',
                      envsIsFirst = isFirst,
                      envsTileLocalIndex = localIdx,
                      envsTileStorageIndex = localIdx
                    }
                  genSequential envs'''' loops' $ ptIn tileLoop
                ptAfter tileLoop envs'''
                return OP_Unit
              )
              -- Parallel mode
              (do
                forM_ ((True, ptFirstLoop tileLoops) : map (False, ) (ptOtherLoops tileLoops)) $ \(isFirstTileLoop, tileLoop) -> do
                  -- All nested loops are placed in the first tile loop by parCodeGens
                  let loops'' = if isFirstTileLoop then loops' else []
                  let ann =
                        -- Only do loop peeling if requested and when there are no nested loops.
                        -- Peeling over nested loops causes a lot of code duplication,
                        -- and is probably not worth it.
                        [ Loop.LoopPeel | cpuLoopPeel (ptAnalysis tileLoop) && null loops'' ]
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

                  ptBefore tileLoop envs'''
                  Loop.loopWith ann (isDescending direction) (OP_Int lower) (OP_Int upper) $ \isFirst idx -> do
                    localIdx <- A.sub numType idx (OP_Int lower)
                    let envs'''' = envs'''{
                        envsLoopDepth = 1,
                        envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs''',
                        envsIsFirst = isFirst,
                        envsTileLocalIndex = localIdx,
                        envsTileStorageIndex = localIdx
                      }
                    genSequential envs'''' loops'' $ ptIn tileLoop
                  ptAfter tileLoop envs'''
                return OP_Unit
              )
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
        value <- instr' $ LLVM.Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
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

type NParLoopCodeGen = ParLoopCodeGen Native CPULoopAnalysis

-- Parallel code generation for one-dimensional collective operations (folds and scans).
-- Other operations, either OpCodeGenSingle or nested deeper, are handled in opCodeGen
parCodeGen :: Bool -> FlatOp NativeOp env idxEnv -> Maybe (Exists (NParLoopCodeGen env idxEnv))
parCodeGen descending (FlatOp NFold
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun (Just seed) input output inputIdx outputIdx
parCodeGen descending (FlatOp NFold1
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun Nothing input output inputIdx outputIdx
parCodeGen descending (FlatOp (NScan1 _)
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenScanLookback descending IsScan fun Nothing input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
parCodeGen descending (FlatOp (NScan' _)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx _ foldOutputIdx :>: _))
  = Just $ parCodeGenScanLookback descending IsScan fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
    (\envs result -> writeArray' envs foldOutput foldOutputIdx result)
parCodeGen descending (FlatOp (NScan dir)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: _ :>: _))
  = case dir of
      LeftToRight -> Just $ parCodeGenScanLookback descending IsScan fun (Just seed) input inputIdx -- Change this for testcase
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\_ _ -> return ())
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
      RightToLeft -> Just $ parCodeGenScanLookback descending IsScan fun (Just seed) input inputIdx
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
parCodeGen _ _ = Nothing

parCodeGenFold
  :: Bool
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e)
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (NParLoopCodeGen env idxEnv)
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
  = parCodeGenScanLookback descending IsFold fun seed input inputIdx
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
  -> Exists (NParLoopCodeGen env idxEnv)
parCodeGenFoldCommutative _ fun seed identity input output inputIdx outputIdx = Exists $ ParLoopCodeGen
  (CPULoopAnalysis False)
  -- In kernel memory, store a lock (Word8) and the
  -- reduced value so far. The lock must be acquired to read or update the total value.
  -- Value 0 means unlocked, 1 is locked.
  (bufferEltsR memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeWord8 0) Nothing -- unlocked
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
  (\_ _ _ _ -> return ())
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
        _ <- instr' $ LLVM.Fence (CrossThread, Release)
        -- TODO: Change to atomic store
        _ <- instr' $ Store Volatile lock (scalar scalarTypeWord8 0) Nothing
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

parCodeGenScanLookback
  :: forall e sh env idxEnv.
     Bool -- Whether the loop is descending
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
  -> Exists (NParLoopCodeGen env idxEnv)
parCodeGenScanLookback descending foldOrScan fun Nothing input index codeSeed codePre codePost codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScanLookback descending foldOrScan fun (Just $ mkConstant tp identity) input index codeSeed codePre codePost codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input -- maak het een struct zodat het de waarde van iets is of  PrimTypetuple
parCodeGenScanLookback descending foldOrScan fun seed input index codeSeed codePre codePost codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (CPULoopAnalysis $ isNothing identity)
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
  (\_ _ -> tupleAlloca tp)
  -- Code before the tile loop
  (\singleThreaded accumVar ptr envs ->
    if singleThreaded then do
      -- In the single threaded mode, we directly do a scan over this tile,
      -- instead of the reduce, lookback and scan phases.
      ptrs <- tuplePtrs' memoryTp ptr
      case ptrs of
        TupRsingle tileArray -> do -- Memory access
          prevIndex <- indexMin1 (envsTileIndex envs)
          safePrevIndex <- A.max singleType (A.liftInt 0) prevIndex
          prefix <- tupleLoadArray tp NonVolatile tileArray (opsToOpInt safePrevIndex) prefixidx

          tupleStore tp accumVar prefix
        --   -- Note: on the first tile, we read an undefined value if there is no
        --   -- seed. This is fine, as we don't use this value in the tile loop.
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
      _ <- putString "From tile loop 1 (singlethreaded)"
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
      _ <- putString "From tile loop 1 (parallel)"
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
    ptrs <- tuplePtrs' memoryTp ptr
    local <- tupleLoad tp accumVar

    isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
    case ptrs of
      TupRsingle tileArray -> do
        newPrefix <- do 
          if singleThreaded then do
            return local
          else do
            -- Special case for folds that do not start sequentially
            A.ifThenElse' (tp, isFirstTile)
              ( do
                return local
              )
              ( do

                -- Store the local result in the tile array
                tupleStoreArray tp NonVolatile tileArray (singleEnvIndex envs) reductionidx local
                _ <- instr' $ LLVM.Fence (CrossThread, Release)
                tupleStoreArray (TupRsingle scalarTypeWord8) NonVolatile tileArray (singleEnvIndex envs) tileFlagidx reductionFlag


                prevIndex <- indexMin1 (envsTileIndex envs)
                maybeStart <- case identity of
                  Just identity' -> do
                    value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
                    return (OP_Pair value word8True)
                  Nothing -> return (OP_Pair local word8False) -- local is used as a dummy value which is never used
                let loopVartp = TupRpair (TupRpair (TupRsingle scalarTypeWord8) (TupRsingle scalarTypeInt)) (TupRpair tp (TupRsingle scalarTypeWord8)) -- scalarTypeWord8 in place of a boolean, 0 for stop looping, 1 for keep looping


                result <- Loop.while [Loop.LoopNonEmpty] loopVartp
                  (\loopVar -> do
                    let OP_Pair (OP_Pair keepLooping _) _ = loopVar

                    A.eq singleType keepLooping word8True -- If keepLooping is 1 (true), keep looping
                  )
                  (\loopVar -> do
                    case loopVar of
                      OP_Pair (OP_Pair _ curIndex) (OP_Pair curReduction hasValue) -> do

                        curFlag <- tupleLoadArray (TupRsingle scalarTypeWord8) Volatile tileArray (opsToOpInt curIndex) tileFlagidx
                        _ <- instr' $ LLVM.Fence (CrossThread, Acquire)


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

                            tupleStore tp accumVar newReduction

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

                                return $ OP_Pair (OP_Pair word8True newIndex) (OP_Pair newReduction word8True)
                            )
                            (do
                              -- putcharStr "flag 0"
                              return loopVar)
                          )
                  )
                  ( OP_Pair (OP_Pair word8True prevIndex) maybeStart
                  )
                let OP_Pair _ (OP_Pair prefix _) = result
                -- Apply the prefix to our local reduction
                ( if envsDescending envs then
                        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
                      else
                        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
                    )
              )

        tupleStoreArray tp NonVolatile tileArray (singleEnvIndex envs) prefixidx newPrefix
        _ <- instr' $ LLVM.Fence (CrossThread, Release)
        tupleStoreArray (TupRsingle scalarTypeWord8) Volatile tileArray (singleEnvIndex envs) tileFlagidx prefixFlag -- Set the flag to 2 (prefix available)

        -- _ <- putInt $ envsTileIndex envs 
        -- putString ": From ptAfter\n"

  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs' memoryTp ptr
    case ptrs of
      TupRsingle tileArray -> do
        prevIndex <- indexMin1 $ OP_Int (envsTileCount envs)
        safePrevIndex <- A.max singleType (A.liftInt 0) prevIndex

        value <- tupleLoadArray tp NonVolatile tileArray (opsToOpInt safePrevIndex) prefixidx

        codeEnd envs value
  )
  -- In the next tile loop, we prefer loop peeling iff there is no seed.
  -- In the first iteration, the first tile loop will then start without a prefix value,
  -- and we thus should do loop peeling there.
  -- Not executed when this tile is executed in the sequential mode.
  (if foldOrScan == IsFold then Nothing else
    Just (CPULoopAnalysis $ isNothing seed, \accumVar _ envs -> do
      -- A.when (return $ envsIsFirst envs) $ do 
      --   -- _ <- putInt $ envsTileIndex envs 
      --   -- putString ": From secondLoop\n"
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
    
    -- tileArray = 
    ArgArray _ (ArrayR _ tp) _ _ = input

    -- flag + reduction + prefix 
    -- Having the type ruins it?
    memoryTp = TupRsingle tileArray
    tileTP :: PrimType (Struct ((Word8, e), e))
    tileTP = StructPrimType False $ 
      TupRsingle (ScalarPrimType scalarTypeWord8) `TupRpair`
      mapTupR ScalarPrimType tp `TupRpair`
      mapTupR ScalarPrimType tp
    tileArray :: PrimType (SizedArray  (Struct ((Word8, e), e)))
    tileArray = ArrayPrimType arraySize tileTP
    arraySize :: Word64 -- Constant array size, is this actually constant?
    arraySize = 32768 
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing
    tileFlagidx = tupleLeft (tupleLeft TupleIdxSelf)
    reductionidx = tupleRight (tupleLeft TupleIdxSelf)
    prefixidx = tupleRight TupleIdxSelf
    singleEnvIndex envs = case envsTileIndex envs of
      OP_Int idx -> idx
    indexMin1 idx = A.sub numType idx (A.liftInt 1)
    opsToOpInt (OP_Int i) = i

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
  -> Exists (NParLoopCodeGen env idxEnv)
parCodeGenScan descending foldOrScan fun Nothing input index codeSeed codePre codePost codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScan descending foldOrScan fun (Just $ mkConstant tp identity) input index codeSeed codePre codePost codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
parCodeGenScan descending foldOrScan fun seed input index codeSeed codePre codePost codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (CPULoopAnalysis $ isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  (bufferEltsR memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeInt 0) Nothing
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
              idx <- instr $ Load Volatile idxPtr Nothing
              A.neq singleType idx (envsTileIndex envs)
            )
            (\_ -> return OP_Unit)
            OP_Unit
          _ <- instr' $ LLVM.Fence (CrossThread, Acquire)
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

        _ <- instr' $ LLVM.Fence (CrossThread, Release)
        OP_Int nextIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
        _ <- instr' $ Store Volatile idxPtr nextIdx Nothing
        return ()
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
    Just (CPULoopAnalysis $ isNothing seed, \accumVar _ envs -> do
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
