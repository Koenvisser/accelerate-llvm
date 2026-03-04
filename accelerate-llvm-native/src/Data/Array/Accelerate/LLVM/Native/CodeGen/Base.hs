{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# OPTIONS_GHC -Wno-orphans     #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Base
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Base
  where

import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.Foreign                    ()
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Elt (bytesElt)
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Operand

import Data.String
import qualified Data.ByteString.Short.Char8                        as S8
import LLVM.AST.Type.Instruction.Volatile (Volatility(NonVolatile))

shardAmount :: Word64
shardAmount = 128

-- The struct passed as argument to a call contains:
--  * work_function: ptr
--  * continuation: ptr, u32 (program, location)
--  * active_threads: u32,
--  * work_index: u64,
--  * In the future, perhaps also store a work_size: u32
-- We store the work function as a pointer to a struct, as that makes it easy
-- to separate pointers to a kernel from pointers to buffers, when compiling
-- a schedule.
type Header = ((((((((Ptr (Struct Int8), Ptr Int8), Word32), Word32), Word64), Ptr Word8), Ptr Word8), SizedArray Word64), Word64)

headerType :: TupR PrimType Header
headerType = TupRsingle (PtrPrimType (StructPrimType False $ TupRsingle primType) defaultAddrSpace)
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle (PtrPrimType primType defaultAddrSpace)
  `TupRpair` TupRsingle (PtrPrimType primType defaultAddrSpace)
  `TupRpair` TupRsingle (ArrayPrimType shardAmount primType)
  `TupRpair` TupRsingle primType

type KernelType env
  -- Ptr to the kernel struct
  = Ptr (Struct ((Header, Struct (MarshalEnv env)), SizedArray Word))
  -- Ptr to the locks array (for any permutes)
  -> Ptr Word8
  -- A magic value for single-threaded initialization or finalization
  -> Word64
  -- Only in initialization, this function returns whether the kernel should run sequentially or in parallel
  -> Word8

bindHeaderEnv
  :: forall env. Env AccessGroundR env
  -> ( PrimType (Ptr (Struct ((Header, Struct (MarshalEnv env)), SizedArray Word)))
     , CodeGen Native ()
     , Operand (Ptr Word8)  -- work indexes of shards
     , Operand (Ptr Word8)  -- work indexes of fold shards
     , Operand (Ptr Word64)       -- Cache line width in bytes
     , Operand (Ptr (SizedArray Word64))  -- sizes of the shards
     , Operand (Ptr Word64)               -- In the case of workassist, the workassist index.
       -- In the case of sharded self scheduling, combined the next shard and amount of finished shards.
     , Operand Word64 -- Flag that specifies if the work needs to be initialized or finished
     , Operand (Ptr (SizedArray Word))
     , Gamma env
     )
bindHeaderEnv env =
  ( argTp
  , do
      shards <- instr' $ GetElementPtr (gepStruct (PtrPrimType primType defaultAddrSpace) arg $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      shardFold <- instr' $ GetElementPtr (gepStruct (PtrPrimType primType defaultAddrSpace) arg $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ nameShards         := LoadPtr NonVolatile shards
      instr_ $ downcast $ nameShardsFold     := LoadPtr NonVolatile shardFold
      instr_ $ downcast $ nameCacheLineWidth := GetElementPtr (gepStruct primType arg $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ nameShardSizes     := GetElementPtr (gepStruct (ArrayPrimType shardAmount (ScalarPrimType scalarType)) arg $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ nameIndex          := GetElementPtr (gepStruct primType arg $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ "env"              := GetElementPtr (gepStruct envTp arg $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ nameKernelMemory   := GetElementPtr (gepStruct kernelMemTp arg $ TupleIdxRight TupleIdxSelf)
      extractEnv
  , LocalReference (PrimType $ PtrPrimType primType defaultAddrSpace) nameShards
  , LocalReference (PrimType $ PtrPrimType primType defaultAddrSpace) nameShardsFold
  , LocalReference (PrimType $ PtrPrimType primType defaultAddrSpace) nameCacheLineWidth
  , LocalReference (PrimType $ PtrPrimType (ArrayPrimType shardAmount (ScalarPrimType scalarType)) defaultAddrSpace) nameShardSizes
  , LocalReference (PrimType $ PtrPrimType (ScalarPrimType scalarType) defaultAddrSpace) nameIndex
  , LocalReference type' nameFlag
  , LocalReference (PrimType $ PtrPrimType kernelMemTp defaultAddrSpace) nameKernelMemory
  , gamma
  )
  where
    -- The Word array at the end is kernel memory. SEE: [Kernel Memory]
    -- Note that the array here has size 0, but it may be larger.
    -- LLVM allows this, since we only use pointer casts here and the allocation does not happen here.
    argTp = PtrPrimType (StructPrimType False (headerType `TupRpair` TupRsingle envTp `TupRpair` TupRsingle kernelMemTp)) defaultAddrSpace
    (envTp, extractEnv, gamma) = bindEnvFromStruct env

    nameShards = "workassist.shards"
    nameShardsFold = "workassist.shards_fold"
    nameCacheLineWidth = "workassist.cache_line_size"
    nameShardSizes = "workassist.shard_sizes"
    nameIndex = "workassist.index"
    nameFlag = "workassist.flag"
    nameKernelMemory = "kernel_memory"

    kernelMemTp :: PrimType (SizedArray Word)
    kernelMemTp = ArrayPrimType 0 primType
    arg = LocalReference (PrimType argTp) "arg"
