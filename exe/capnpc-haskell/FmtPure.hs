{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
-- Generate idiomatic haskell data types from the types in IR.
module FmtPure
    ( fmtModule
    ) where

import IR

import Data.Capnp.Core.Schema (Id)
import Data.Monoid            (mconcat, (<>))
import GHC.Exts               (IsList(..))
import Text.Printf            (printf)
import Util                   (mintercalate)

import qualified Data.Text              as T
import qualified Data.Text.Lazy.Builder as TB

-- | If a module reference refers to a generated module, does it
-- refer to the raw, low-level module or the *.Pure variant (which
-- this module generates)?
data ModRefType = Pure | Raw
    deriving(Show, Read, Eq)

fmtName :: ModRefType -> Id -> Name -> TB.Builder
fmtName refTy thisMod Name{..} = modPrefix <> localName
  where
    localName = mintercalate "'" $
        map TB.fromText $ fromList $ toList nameLocalNS ++ [nameUnqualified]
    modPrefix
        | null nsParts = ""
        | refTy == Pure && modRefToNS refTy (ByCapnpId thisMod) == ns = ""
        | otherwise = fmtModRef refTy nameModule <> "."
    ns@(Namespace nsParts) = modRefToNS refTy nameModule

modRefToNS :: ModRefType -> ModuleRef -> Namespace
modRefToNS _ (FullyQualified ns) = ns
modRefToNS ty (ByCapnpId id) = Namespace $ case ty of
    Pure -> ["Data", "Capnp", "ById", T.pack (printf "X%x" id), "Pure"]
    Raw  -> ["Data", "Capnp", "ById", T.pack (printf "X%x" id)]

fmtModule :: Module -> TB.Builder
fmtModule Module{..} = mintercalate "\n"
    [ "{-# LANGUAGE DuplicateRecordFields #-}"
    , "{-# LANGUAGE FlexibleInstances #-}"
    , "{-# LANGUAGE MultiParamTypeClasses #-}"
    , "{-# OPTIONS_GHC -Wno-unused-imports #-}"
    , "module "
        <> fmtModRef Pure (ByCapnpId modId)
        <> " where"
    , ""
    , "-- Code generated by capnpc-haskell. DO NOT EDIT."
    , "-- Generated from schema file: " <> TB.fromText modFile
    , ""
    , "import Data.Int"
    , "import Data.Word"
    , ""
    , "import Data.Capnp.Untyped.Pure (List)"
    , "import Data.Capnp.BuiltinTypes.Pure (Data, Text)"
    , ""
    , "import qualified Data.Capnp.Untyped.Pure"
    , "import qualified Data.Capnp.Untyped"
    , "import qualified Codec.Capnp"
    , ""
    , fmtImport Raw $ Import (ByCapnpId modId)
    , mintercalate "\n" $ map (fmtImport Pure) modImports
    , mintercalate "\n" $ map (fmtImport Raw) modImports
    , ""
    , mconcat $ map (fmtDataDef modId) modDefs
    ]

fmtImport :: ModRefType -> Import -> TB.Builder
fmtImport ty (Import ref) = "import qualified " <> fmtModRef ty ref

fmtModRef :: ModRefType -> ModuleRef -> TB.Builder
fmtModRef ty ref = mintercalate "." (map TB.fromText $ toList $ modRefToNS ty ref)

fmtType :: Id -> Type -> TB.Builder
fmtType thisMod (Type name params) =
    fmtName Pure thisMod name
    <> mconcat [" (" <> fmtType thisMod ty <> ")" | ty <- params]
fmtType thisMod (ListOf eltType) = "List (" <> fmtType thisMod eltType <> ")"
fmtType thisMod (PrimType prim)  = fmtPrimType prim
fmtType thisMod (Untyped ty)     = "Maybe (" <> fmtUntyped ty <> ")"

fmtPrimType :: PrimType -> TB.Builder
fmtPrimType PrimInt{isSigned=True,size}  = "Int" <> TB.fromString (show size)
fmtPrimType PrimInt{isSigned=False,size} = "Word" <> TB.fromString (show size)
fmtPrimType PrimFloat32                  = "Float"
fmtPrimType PrimFloat64                  = "Double"
fmtPrimType PrimBool                     = "Bool"
fmtPrimType PrimText                     = "Text"
fmtPrimType PrimData                     = "Data"
fmtPrimType PrimVoid                     = "()"

fmtUntyped :: Untyped -> TB.Builder
fmtUntyped Struct = "Data.Capnp.Untyped.Pure.Struct"
fmtUntyped List   = "Data.Capnp.Untyped.Pure.List'"
fmtUntyped Cap    = "Data.Capnp.Untyped.Pure.Cap"
fmtUntyped Ptr    = "Data.Capnp.Untyped.Pure.PtrType"

fmtVariant :: Id -> Variant -> TB.Builder
fmtVariant thisMod Variant{variantName,variantParams} =
    fmtName Pure thisMod variantName
    <> case variantParams of
        NoParams -> ""
        Unnamed ty _ -> " (" <> fmtType thisMod ty <> ")"
        Record [] -> ""
        Record fields -> mconcat
            [ "\n        { "
            , mintercalate "\n        , " $ map (fmtField thisMod) fields
            ,  "\n        }"
            ]

fmtField :: Id -> Field -> TB.Builder
fmtField thisMod Field{fieldName,fieldType} =
    TB.fromText fieldName <> " :: " <> fmtType thisMod fieldType

fmtDataDef ::  Id -> DataDef -> TB.Builder
fmtDataDef thisMod DataDef{dataName,dataVariants,dataCerialType} = mconcat
    [ "data ", fmtName Pure thisMod dataName, "\n    = "
    , mintercalate "\n    | " $ map (fmtVariant thisMod) dataVariants
    , "\n    deriving(Show, Read, Eq)\n\n"
    ] <>
    case (dataVariants, dataCerialType) of
        ([variant], CTyStruct) ->
            -- The raw module just has this as a newtype wrapper. Let's
            -- generate an IsStruct instance and a Decerialize instance.
            let rawName = fmtName Raw thisMod dataName
                pureName = fmtName Pure thisMod dataName
            in mconcat
                -- The IsStruct instance is just a wrapper around decerialize:
                [ "instance Data.Capnp.Untyped.ReadCtx m b\n"
                , "    => Codec.Capnp.IsStruct m ", pureName, " b\n"
                , "  where\n"
                , "    fromStruct = Codec.Capnp.decerialize . ", rawName, "\n"
                , "\n"
                -- This is the thing that does the work:
                , "instance Data.Capnp.Untyped.ReadCtx m b => Codec.Capnp.Decerialize ("
                , rawName
                , " m b) "
                , pureName
                , " where\n"
                , "    decerialize raw = undefined\n" -- TODO: parse fields.
                ]
        _ ->
            -- Don't know what to do with this yet.
            ""
