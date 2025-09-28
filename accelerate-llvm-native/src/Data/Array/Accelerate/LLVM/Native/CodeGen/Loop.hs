{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications    #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Native.Loop
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
  where

-- accelerate
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape                   hiding ( eq )

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                hiding ( lift )
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic      as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop            as Loop

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile
import qualified LLVM.AST.Type.Instruction.RMW as RMW
import Control.Monad (void)
import Control.Monad.Trans
import Control.Monad.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import LLVM.AST.Type.Function
import LLVM.AST.Type.Name

-- | A standard 'for' loop, that steps from the start to end index executing the
-- given function at each index.
--
imapFromTo
    :: Operands Int                                   -- ^ starting index (inclusive)
    -> Operands Int                                   -- ^ final index (exclusive)
    -> (Operands Int -> CodeGen Native ())            -- ^ apply at each index
    -> CodeGen Native ()
imapFromTo start end body =
  Loop.imapFromStepTo [] start (liftInt 1) end body


-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromTo
    :: [Loop.LoopAnnotation]                                     -- ^ annotations for all but the innermost loop
    -> [Loop.LoopAnnotation]                                     -- ^ annotations for the innermost loop
    -> ShapeR sh
    -> Operands sh                                          -- ^ initial index (inclusive)
    -> Operands sh                                          -- ^ final index (exclusive)
    -> Operands sh                                          -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromTo annOuter annInner shr start end extent body =
  go shr start end body'
  where
    body' ix = body ix =<< intOfIndex shr extent ix

    go :: ShapeR t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go ShapeRz OP_Unit OP_Unit k
      = k OP_Unit

    go (ShapeRsnoc shr') (OP_Pair ssh ssz) (OP_Pair esh esz) k
      = go shr' ssh esh
      $ \sz      -> Loop.imapFromStepTo ann ssz (liftInt 1) esz
      $ \i       -> k (OP_Pair sz i)
      where
        ann = case shr' of
          ShapeRz -> annInner
          _ -> annOuter

{--
-- TLM: this version (seems to) compute the corresponding linear index as it
--      goes. We need to compare it against the above implementation to see if
--      there are any advantages.
--
imapNestFromTo'
    :: forall sh. Shape sh
    => Operands sh
    -> Operands sh
    -> Operands sh
    -> (Operands sh -> Operands Int -> CodeGen Native ())
    -> CodeGen Native ()
imapNestFromTo' start end extent body = do
  startl <- intOfIndex extent start
  void $ go (eltType @sh) start end extent (int 1) startl body'
  where
    body' :: Operands (EltRepr sh) -> Operands Int -> CodeGen Native (Operands Int)
    body' ix l = body ix l >> add numType (int 1) l

    go :: TupleType t
       -> Operands t
       -> Operands t
       -> Operands t
       -> Operands Int
       -> Operands Int
       -> (Operands t -> Operands Int -> CodeGen Native (Operands Int))
       -> CodeGen Native (Operands Int)
    go TypeRunit OP_Unit OP_Unit OP_Unit _delta l k
      = k OP_Unit l

    go (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair esh esz) (OP_Pair exh exz) delta l k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = do
          delta' <- mul numType delta exz
          go tsh ssh esh exh delta' l $ \sz ll -> do
            Loop.iterFromStepTo ssz (int 1) esz ll $ \i l' ->
              k (OP_Pair sz i) l'
            add numType ll delta'

    go _ _ _ _ _ _ _
      = $internalError "imapNestFromTo'" "expected shape with Int components"
--}

{--
-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromStepTo
    :: forall sh. Shape sh
    => Operands sh                                    -- ^ initial index (inclusive)
    -> Operands sh                                    -- ^ steps
    -> Operands sh                                    -- ^ final index (exclusive)
    -> Operands sh                                    -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromStepTo start steps end extent body =
  go (eltType @sh) start steps end (body' . IR)
  where
    body' ix = body ix =<< intOfIndex extent ix

    go :: TupleType t -> Operands t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go TypeRunit OP_Unit OP_Unit OP_Unit k
      = k OP_Unit

    go (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair sts stz) (OP_Pair esh esz) k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = go tsh ssh sts esh
      $ \sz      -> Loop.imapFromStepTo ssz stz esz
      $ \i       -> k (OP_Pair sz i)

    go _ _ _ _ _
      = $internalError "imapNestFromTo" "expected shape with Int components"
--}

-- | Iterate with an accumulator between the start and end index, executing the
-- given function at each.
--
iterFromTo
    :: TypeR a
    -> Operands Int                                       -- ^ starting index (inclusive)
    -> Operands Int                                       -- ^ final index (exclusive)
    -> Operands a                                         -- ^ initial value
    -> (Operands Int -> Operands a -> CodeGen Native (Operands a))    -- ^ apply at each index
    -> CodeGen Native (Operands a)
iterFromTo tp start end seed body =
  Loop.iterFromStepTo [] tp start (liftInt 1) end seed body

workassistLoop
    :: Operand (Ptr Word64)                 -- index into work
    -> Operand Word64                       -- size of total work
    -> (Operand Bool -> Operand Word64 -> CodeGen Native ())
    -> CodeGen Native ()
workassistLoop counter size doWork = do
  entry    <- getBlock
  work     <- newBlock "workassist.loop.work"
  claimed  <- newBlock "workassist.all.claimed"
  exit     <- newBlock "workassist.exit"
  finished <- newBlock "workassist.finished"

  firstIndex <- atomicAdd Monotonic counter (integral TypeWord64 1)

  initialCondition <- lt singleType (OP_Word64 firstIndex) (OP_Word64 size)
  initialSeq <- eq singleType (OP_Word64 firstIndex) (liftWord64 0)
  _ <- cbr initialCondition work exit

  _ <- setBlock work
  let indexName = "block_index"
  -- Whether the thread should operate in the single threaded mode of
  -- zero-overhead parallel scans.
  let seqName = "sequential_mode"
  let seqMode = LocalReference type' seqName
  let index = LocalReference type' indexName

  doWork seqMode index

  nextIndex <- atomicAdd Monotonic counter (integral TypeWord64 1)
  condition <- lt singleType (OP_Word64 nextIndex) (OP_Word64 size)
  indexPlusOne <- add numType (OP_Word64 index) (liftWord64 1)
  nextSeq' <- eq singleType indexPlusOne (OP_Word64 nextIndex)
  -- Continue in sequential mode if the newly claimed block directly follows
  -- the previous block, and we were still in the sequential mode.
  nextSeq <- land nextSeq' (OP_Bool seqMode)

  -- Append the phi node to the start of the 'work' block.
  -- We can only do this now, as we need to have 'nextIndex', and know the
  -- exit block of 'doWork'.
  currentBlock <- getBlock
  phi1 work indexName [(firstIndex, entry), (nextIndex, currentBlock)]
  phi1 work seqName [(op BoolPrimType initialSeq, entry), (op BoolPrimType nextSeq, currentBlock)]

  cbr condition work exit

  setBlock exit
  retval_ $ scalar (scalarType @Word8) 0

chunkTileStartSize :: ShapeR sh -> Operands sh -> Int -> Int -> CodeGen Native (Operands sh)
chunkTileStartSize ShapeRz OP_Unit _ _ = return OP_Unit
chunkTileStartSize (ShapeRsnoc shr) (OP_Pair sh sz) threads maxTileSize = do
  starts <- chunkTileStartSize shr sh threads maxTileSize
  -- f = I / 2 * threads, l = 1
  f' <- A.quot TypeInt sz (A.liftInt $ 2 * threads)
  f <- A.min singleType f' (A.liftInt maxTileSize)

  return $ OP_Pair starts f

chunkTileDecrStep :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkTileDecrStep ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkTileDecrStep (ShapeRsnoc shr) (OP_Pair fs f) (OP_Pair chunkSh chunkSz) = do
  steps <- chunkTileDecrStep shr fs chunkSh
  -- decr = (f - l) / (N - 1)
  let l = A.liftInt 1
  numerator <- A.sub numType f l
  denom <- A.sub numType chunkSz (A.liftInt 1)
  step <- A.quot TypeInt numerator denom
  return $ OP_Pair steps step

chunkCount :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkCount ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkCount (ShapeRsnoc shr) (OP_Pair sh sz) (OP_Pair fs f) = do
  counts <- chunkCount shr sh fs
  -- N = 2 * I / (f + l)
  -- f = I / 2 * threads, l = 1
  let l = A.liftInt 1
  numerator <- A.mul numType (A.liftInt 2) sz
  denom <- A.add numType f l
  count <- A.quot TypeInt numerator denom

  return $ OP_Pair counts count

chunkBounds
  :: ShapeR sh 
  -> Operands sh -- Dimension size
  -> Operands sh -- Chunk index
  -> Operands sh -- First chunk size
  -> Operands sh -- Decrement step
  -> CodeGen Native (Operands sh, Operands sh)
chunkBounds ShapeRz OP_Unit OP_Unit OP_Unit OP_Unit = return (OP_Unit, OP_Unit)
chunkBounds (ShapeRsnoc shr) (OP_Pair sh sz) (OP_Pair idxSh idx) (OP_Pair fs f) (OP_Pair decrSh decrStep) = do
  (startIxs, endIxs) <- chunkBounds shr sh idxSh fs decrSh
  -- = tileIdx * firstSize - dec * (tileIdx * (tileIdx - 1)) / 2
  -- or more simply: sum_{i=0}^{tileIdx-1} (firstSize - i * dec)
  -- a = tileIdx * firstSize
  a <- A.mul numType idx f
  -- b = tileIdx * (tileIdx - 1)
  t1 <- A.sub numType idx (A.liftInt 1)
  b  <- A.mul numType idx t1
  -- half = b / 2
  half <- A.quot TypeInt b (A.liftInt 2)
  -- decPart = dec * half
  decPart <- A.mul numType decrStep half
  -- result = a - decPart
  start <- A.sub numType a decPart
  decr <- A.mul numType decrStep idx
  tileSize <- A.sub numType f decr
  end <- A.add numType start tileSize
  end' <- A.min singleType end sz

  return (OP_Pair startIxs start, OP_Pair endIxs end')

atomicAdd :: MemoryOrdering -> Operand (Ptr Word64) -> Operand Word64 -> CodeGen Native (Operand Word64)
atomicAdd ordering ptr increment = do
  instr' $ AtomicRMW numType NonVolatile RMW.Add ptr increment (CrossThread, ordering)

atomicRead :: MemoryOrdering -> Operand (Ptr Word64) -> CodeGen Native (Operand Word64)
-- TODO: actually use load
atomicRead ordering ptr = atomicAdd ordering ptr (integral TypeWord64 0)

---- debugging tools ----
putchar :: Operands Int -> CodeGen Native (Operands Int)
putchar x = call (lamUnnamed primType $ Body (PrimType primType) Nothing (Label "putchar")) 
                 (ArgumentsCons (op TypeInt x) [] ArgumentsNil) 
                 []
putcharA, putcharB, putcharC, putcharD, putcharE, putcharF, putcharG, putcharH :: CodeGen Native ()
putcharA = void $ putchar $ liftInt 65
putcharB = void $ putchar $ liftInt 66
putcharC = void $ putchar $ liftInt 67
putcharD = void $ putchar $ liftInt 68
putcharE = void $ putchar $ liftInt 69
putcharF = void $ putchar $ liftInt 70
putcharG = void $ putchar $ liftInt 71
putcharH = void $ putchar $ liftInt 72
