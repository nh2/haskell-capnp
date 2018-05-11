{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Capnp.ById.Xa93fc509624c72d9.Pure where

-- generated from /usr/include/capnp/schema.capnp

import Data.Int
import Data.Word

import Data.Capnp.Untyped.Pure (List)
import Data.Capnp.BuiltinTypes.Pure (Data, Text)

import qualified Data.Capnp.Untyped.Pure
import qualified Codec.Capnp

import qualified Data.Capnp.ById.Xbdf87d7bb8304e81.Pure

data Type'anyPointer'unconstrained
    = Type'anyPointer'unconstrained
        { union' :: Type'anyPointer'unconstrained'
        }
    deriving(Show, Read, Eq)

data Type'anyPointer'unconstrained'
    = Type'anyPointer'unconstrained'anyKind
    | Type'anyPointer'unconstrained'struct
    | Type'anyPointer'unconstrained'list
    | Type'anyPointer'unconstrained'capability
    deriving(Show, Read, Eq)

data Brand
    = Brand
        { scopes :: List (Brand'Scope)
        }
    deriving(Show, Read, Eq)

data Method
    = Method
        { name :: Text
        , codeOrder :: Word16
        , paramStructType :: Word64
        , resultStructType :: Word64
        , annotations :: List (Annotation)
        , paramBrand :: Brand
        , resultBrand :: Brand
        , implicitParameters :: List (Node'Parameter)
        }
    deriving(Show, Read, Eq)

data Enumerant
    = Enumerant
        { name :: Text
        , codeOrder :: Word16
        , annotations :: List (Annotation)
        }
    deriving(Show, Read, Eq)

data Field
    = Field
        { name :: Text
        , codeOrder :: Word16
        , annotations :: List (Annotation)
        , discriminantValue :: Word16
        , ordinal :: Field'ordinal
        , union' :: Field'
        }
    deriving(Show, Read, Eq)

data Field'
    = Field'slot
        { offset :: Word32
        , type_ :: Type
        , defaultValue :: Value
        , hadExplicitDefault :: Bool
        }
    | Field'group
        { typeId :: Word64
        }
    deriving(Show, Read, Eq)

data Superclass
    = Superclass
        { id :: Word64
        , brand :: Brand
        }
    deriving(Show, Read, Eq)

data Brand'Scope
    = Brand'Scope
        { scopeId :: Word64
        , union' :: Brand'Scope'
        }
    deriving(Show, Read, Eq)

data Brand'Scope'
    = Brand'Scope'bind (List (Brand'Binding))
    | Brand'Scope'inherit
    deriving(Show, Read, Eq)

data CodeGeneratorRequest'RequestedFile'Import
    = CodeGeneratorRequest'RequestedFile'Import
        { id :: Word64
        , name :: Text
        }
    deriving(Show, Read, Eq)

data Node'Parameter
    = Node'Parameter
        { name :: Text
        }
    deriving(Show, Read, Eq)

data Field'ordinal
    = Field'ordinal
        { union' :: Field'ordinal'
        }
    deriving(Show, Read, Eq)

data Field'ordinal'
    = Field'ordinal'implicit
    | Field'ordinal'explicit (Word16)
    deriving(Show, Read, Eq)

data CodeGeneratorRequest
    = CodeGeneratorRequest
        { nodes :: List (Node)
        , requestedFiles :: List (CodeGeneratorRequest'RequestedFile)
        , capnpVersion :: CapnpVersion
        }
    deriving(Show, Read, Eq)

data Type'anyPointer
    = Type'anyPointer
        { union' :: Type'anyPointer'
        }
    deriving(Show, Read, Eq)

data Type'anyPointer'
    = Type'anyPointer'unconstrained
        { union' :: Type'anyPointer'unconstrained'
        }
    | Type'anyPointer'parameter
        { scopeId :: Word64
        , parameterIndex :: Word16
        }
    | Type'anyPointer'implicitMethodParameter
        { parameterIndex :: Word16
        }
    deriving(Show, Read, Eq)

data Brand'Binding
    = Brand'Binding
        { union' :: Brand'Binding'
        }
    deriving(Show, Read, Eq)

data Brand'Binding'
    = Brand'Binding'unbound
    | Brand'Binding'type_ (Type)
    deriving(Show, Read, Eq)

data Value
    = Value
        { union' :: Value'
        }
    deriving(Show, Read, Eq)

data Value'
    = Value'void
    | Value'bool (Bool)
    | Value'int8 (Int8)
    | Value'int16 (Int16)
    | Value'int32 (Int32)
    | Value'int64 (Int64)
    | Value'uint8 (Word8)
    | Value'uint16 (Word16)
    | Value'uint32 (Word32)
    | Value'uint64 (Word64)
    | Value'float32 (Float)
    | Value'float64 (Double)
    | Value'text (Text)
    | Value'data_ (Data)
    | Value'list (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    | Value'enum (Word16)
    | Value'struct (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    | Value'interface
    | Value'anyPointer (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    deriving(Show, Read, Eq)

data CodeGeneratorRequest'RequestedFile
    = CodeGeneratorRequest'RequestedFile
        { id :: Word64
        , filename :: Text
        , imports :: List (CodeGeneratorRequest'RequestedFile'Import)
        }
    deriving(Show, Read, Eq)

data Type
    = Type
        { union' :: Type'
        }
    deriving(Show, Read, Eq)

data Type'
    = Type'void
    | Type'bool
    | Type'int8
    | Type'int16
    | Type'int32
    | Type'int64
    | Type'uint8
    | Type'uint16
    | Type'uint32
    | Type'uint64
    | Type'float32
    | Type'float64
    | Type'text
    | Type'data_
    | Type'list
        { elementType :: Type
        }
    | Type'enum
        { typeId :: Word64
        , brand :: Brand
        }
    | Type'struct
        { typeId :: Word64
        , brand :: Brand
        }
    | Type'interface
        { typeId :: Word64
        , brand :: Brand
        }
    | Type'anyPointer
        { union' :: Type'anyPointer'
        }
    deriving(Show, Read, Eq)

data ElementSize
    = ElementSize'empty
    | ElementSize'bit
    | ElementSize'byte
    | ElementSize'twoBytes
    | ElementSize'fourBytes
    | ElementSize'eightBytes
    | ElementSize'pointer
    | ElementSize'inlineComposite
    | ElementSize'unknown' (Word16)
    deriving(Show, Read, Eq)

data CapnpVersion
    = CapnpVersion
        { major :: Word16
        , minor :: Word8
        , micro :: Word8
        }
    deriving(Show, Read, Eq)

data Node'NestedNode
    = Node'NestedNode
        { name :: Text
        , id :: Word64
        }
    deriving(Show, Read, Eq)

data Node
    = Node
        { id :: Word64
        , displayName :: Text
        , displayNamePrefixLength :: Word32
        , scopeId :: Word64
        , nestedNodes :: List (Node'NestedNode)
        , annotations :: List (Annotation)
        , parameters :: List (Node'Parameter)
        , isGeneric :: Bool
        , union' :: Node'
        }
    deriving(Show, Read, Eq)

data Node'
    = Node'file
    | Node'struct
        { dataWordCount :: Word16
        , pointerCount :: Word16
        , preferredListEncoding :: ElementSize
        , isGroup :: Bool
        , discriminantCount :: Word16
        , discriminantOffset :: Word32
        , fields :: List (Field)
        }
    | Node'enum
        { enumerants :: List (Enumerant)
        }
    | Node'interface
        { methods :: List (Method)
        , superclasses :: List (Superclass)
        }
    | Node'const
        { type_ :: Type
        , value :: Value
        }
    | Node'annotation
        { type_ :: Type
        , targetsFile :: Bool
        , targetsConst :: Bool
        , targetsEnum :: Bool
        , targetsEnumerant :: Bool
        , targetsStruct :: Bool
        , targetsField :: Bool
        , targetsUnion :: Bool
        , targetsGroup :: Bool
        , targetsInterface :: Bool
        , targetsMethod :: Bool
        , targetsParam :: Bool
        , targetsAnnotation :: Bool
        }
    deriving(Show, Read, Eq)

data Annotation
    = Annotation
        { id :: Word64
        , value :: Value
        , brand :: Brand
        }
    deriving(Show, Read, Eq)

