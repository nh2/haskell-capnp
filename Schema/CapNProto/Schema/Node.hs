module Schema.CapNProto.Schema.Node where

import qualified Data.CapNProto.Schema as DS

import Data.Text (Text)
import Data.Word (Word16, Word32)
import Schema.CapNProto.Schema as S

id :: DS.Field S.Node Id
id = DS.fromBits 0 64

displayName :: DS.Field S.Node Text
displayName = DS.ptrField 0

displayNamePrefixLength :: DS.Field S.Node Text
displayNamePrefixLength = DS.fromBits 64 96

scopeId :: DS.Field S.Node Id
scopeId = DS.fromBits 128 192

parameters :: DS.Field S.Node (DS.List Parameter)
parameters = DS.ptrField 5

isGeneric :: DS.Field S.Node Bool
isGeneric = DS.fromBits 288 289

nestedNodes :: DS.Field S.Node (DS.List NestedNode)
nestedNodes = DS.ptrField 1

annotations :: DS.Field S.Node (DS.List Annotation)
annotations = DS.ptrField 2

data Parameter = Parameter
data NestedNode = NestedNode

data Union_ = Union_

file :: DS.Field Union_ ()
file = (DS.fromBits 0 0) { DS.fieldTag = Just 0 }

struct :: DS.Field Union_ Union_struct
struct = DS.Field DS.GroupField (Just 1)

data Union_struct = Union_struct

dataWordCount :: DS.Field Union_struct Word16
dataWordCount = DS.fromBits 112 128

pointerCount :: DS.Field Union_struct Word16
pointerCount = DS.fromBits 192 208

preferredListEncoding :: DS.Field Union_struct S.ElementSize
preferredListEncoding = DS.fromBits 208 224

isGroup :: DS.Field Union_struct Bool
isGroup = DS.fromBits 224 225

discriminantCount :: DS.Field Union_struct Word16
discriminantCount = DS.fromBits 240 256

discriminantOffset :: DS.Field Union_struct Word32
discriminantOffset = DS.fromBits 256 288