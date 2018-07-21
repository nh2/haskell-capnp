-- Generate low-level accessors from type types in IR.
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Backends.Raw
    ( fmtModule
    ) where

import IR
import Util

import Data.List   (sortOn)
import Data.Monoid ((<>))
import Data.Ord    (Down(..))
import Text.Printf (printf)

import qualified Data.Text              as T
import qualified Data.Text.Lazy.Builder as TB

-- | Sort varaints by their tag, in decending order (with no tag at all being last).
sortVariants = sortOn (Down . variantTag)

fmtModule :: Module -> [(FilePath, TB.Builder)]
fmtModule Module{modName=Namespace modNameParts,..} =
    [ ( T.unpack $ mintercalate "/" humanParts <> ".hs"
      , mainContent
      )
    , ( printf "Capnp/ById/X%x.hs" modId
      , mconcat
        [ "{-# OPTIONS_GHC -Wno-unused-imports #-}\n"
        , TB.fromString (printf "module Capnp.ById.X%x" modId), "(module ", humanMod, ") where\n"
        , "import ", humanMod
        ]
      )
    ] where
  humanMod = fmtModRef $ FullyQualified $ Namespace humanParts
  humanParts = "Capnp":modNameParts
  mainContent = mintercalate "\n"
    [ "{-# OPTIONS_GHC -Wno-unused-imports #-}"
    , "{-# LANGUAGE FlexibleContexts #-}"
    , "{-# LANGUAGE FlexibleInstances #-}"
    , "{-# LANGUAGE MultiParamTypeClasses #-}"
    , "{-# LANGUAGE TypeFamilies #-}"
    , "{-# LANGUAGE DataKinds #-}"
    , "module " <> fmtModRef (FullyQualified $ Namespace ("Capnp":modNameParts)) <> " where"
    , ""
    , "-- Code generated by capnpc-haskell. DO NOT EDIT."
    , "-- Generated from schema file: " <> TB.fromText modFile
    , ""
    , "import Data.Int"
    , "import Data.Word"
    , ""
    , "import GHC.OverloadedLabels"
    , ""
    , "import qualified Data.Capnp as DC'"
    , "import Data.Capnp.Bits (Word1)"
    , ""
    , "import qualified Data.Bits"
    , "import qualified Data.Maybe"
    -- The trailing ' is to avoid possible name collisions:
    , "import qualified Codec.Capnp as C'"
    , "import qualified Data.Capnp.Basics as B'"
    , "import qualified Data.Capnp.TraversalLimit as TL'"
    , "import qualified Data.Capnp.Untyped as U'"
    , "import qualified Data.Capnp.Message as M'"
    , ""
    , mintercalate "\n" $ map fmtImport modImports
    , ""
    , mintercalate "\n" $ map (fmtDecl modId) modDecls
    ]

fmtModRef :: ModuleRef -> TB.Builder
fmtModRef (ByCapnpId id) = TB.fromString $ printf "Capnp.ById.X%x" id
fmtModRef (FullyQualified (Namespace ns)) = mintercalate "." (map TB.fromText ns)

fmtImport :: Import -> TB.Builder
fmtImport (Import ref) = "import qualified " <> fmtModRef ref

-- | format the IsPtr instance for a list of the struct type with
-- the given name.
fmtStructListIsPtr :: TB.Builder -> TB.Builder
fmtStructListIsPtr nameText = mconcat
    [ "instance C'.IsPtr msg (B'.List msg (", nameText, " msg)) where\n"
    , "    fromPtr msg ptr = List_", nameText, " <$> C'.fromPtr msg ptr\n"
    , "    toPtr (List_", nameText, " l) = C'.toPtr l\n"
    ]

fmtNewtypeStruct :: Id -> Name -> TB.Builder
fmtNewtypeStruct thisMod name =
    let nameText = fmtName thisMod name
    in mconcat
        [ "newtype ", nameText, " msg = ", nameText, " (U'.Struct msg)"
        , "\n\n"
        , "instance C'.IsStruct msg (", nameText, " msg) where\n"
        , "    fromStruct = pure . ", nameText, "\n"
        , "instance C'.IsPtr msg (", nameText, " msg) where\n"
        , "    fromPtr msg ptr = ", nameText, " <$> C'.fromPtr msg ptr\n"
        , "    toPtr (", nameText, " struct) = C'.toPtr struct\n"
        , fmtStructListElem nameText
        , "instance B'.MutListElem s (", nameText, " (M'.MutMsg s)) where\n"
        , "    setIndex (", nameText, " elt) i (List_", nameText, " l) = U'.setIndex elt i l\n"
        , "\n"
        , fmtStructListIsPtr nameText
        ]

-- | Generate an instance of ListElem for a struct type. The parameter is the name of
-- the type constructor.
fmtStructListElem :: TB.Builder -> TB.Builder
fmtStructListElem nameText = mconcat
    [ "instance B'.ListElem msg (", nameText, " msg) where\n"
    , "    newtype List msg (", nameText, " msg) = List_", nameText, " (U'.ListOf msg (U'.Struct msg))\n"
    , "    length (List_", nameText, " l) = U'.length l\n"
    , "    index i (List_", nameText, " l) = U'.index i l >>= ", fmtRestrictedFromStruct nameText, "\n"
    ]

-- | Output an expression equivalent to fromStruct, but restricted to the type
-- with the given type constructor (which must have kind * -> *).
fmtRestrictedFromStruct :: TB.Builder -> TB.Builder
fmtRestrictedFromStruct nameText = mconcat
    [ "(let {"
    , "go :: U'.ReadCtx m msg => U'.Struct msg -> m (", nameText, " msg); "
    , "go = C'.fromStruct"
    , "} in go)"
    ]

-- | Generate a call to 'C'.getWordField' based on a 'DataLoc'.
-- The first argument is an expression for the struct.
fmtGetWordField :: TB.Builder -> DataLoc -> TB.Builder
fmtGetWordField struct DataLoc{..} = mintercalate " "
    [ " C'.getWordField"
    , struct
    , TB.fromString (show dataIdx)
    , TB.fromString (show dataOff)
    , TB.fromString (show dataDef)
    ]

-- | @'fmtSetWordField' struct value loc@ is like 'fmtGetWordField', except that
-- it generates a call to 'setWordField'. The extra value parameter corresponds
-- to the extra parameter in 'setWordField'.
fmtSetWordField :: TB.Builder -> TB.Builder -> DataLoc -> TB.Builder
fmtSetWordField struct value DataLoc{..} = mintercalate " "
    [ " C'.setWordField"
    , struct
    , value
    , TB.fromString (show dataIdx)
    , TB.fromString (show dataOff)
    , TB.fromString (show dataDef)
    ]

fmtFieldAccessor :: Id -> Name -> Name -> Field -> TB.Builder
fmtFieldAccessor thisMod typeName variantName Field{..} =
    let accessorName prefix = fmtName thisMod $ prefixName prefix (subName variantName fieldName)
    in mintercalate "\n"
        [ fmtGetter (accessorName "get_")
        , fmtHas    (accessorName "has_")
        , fmtSetter (accessorName "set_")
        ]
  where
    fmtGetter getName = mconcat
        [ getName, " :: U'.ReadCtx m msg => "
        , fmtName thisMod typeName, " msg -> m ", fmtType thisMod "msg" fieldType, "\n"
        , getName
        , " (", fmtName thisMod typeName, " struct) =", case fieldLoc of
            DataField loc -> fmtGetWordField "struct" loc
            PtrField idx -> mconcat
                [ "\n    U'.getPtr ", TB.fromString (show idx), " struct"
                , "\n    >>= C'.fromPtr (U'.message struct)"
                , "\n"
                ]
            HereField -> " C'.fromStruct struct"
            VoidField -> " Data.Capnp.TraversalLimit.invoice 1 >> pure ()"
        , "\n"
        , "instance U'.ReadCtx m msg => IsLabel ", TB.fromString (show fieldName)
        , " (DC'.Get m (", fmtName thisMod typeName, " msg) (", fmtType thisMod "msg" fieldType, ")) where\n"
        , "    fromLabel = DC'.Get ", getName, "\n"
        ]
    fmtHas hasName = mconcat
        [ hasName, " :: U'.ReadCtx m msg => ", fmtName thisMod typeName, " msg -> m Bool\n"
        , hasName, "(", fmtName thisMod typeName, " struct) = "
        , case fieldLoc of
            DataField DataLoc{dataIdx} ->
                "pure $ " <> TB.fromString (show dataIdx) <> " < U'.length (U'.dataSection struct)"
            PtrField idx ->
                "Data.Maybe.isJust <$> U'.getPtr " <> TB.fromString (show idx) <> " struct"
            HereField -> "pure True"
            VoidField -> "pure True"
        , "\n"
        , "instance U'.ReadCtx m msg => IsLabel ", TB.fromString (show fieldName)
        , " (DC'.Has m (", fmtName thisMod typeName, " msg)) where\n"
        , "    fromLabel = DC'.Has ", hasName, "\n"
        ]
    fmtSetter setName = mconcat
        [ setName, " :: (U'.ReadCtx m (M'.MutMsg s), M'.WriteCtx m s) => "
        , fmtName thisMod typeName, " (M'.MutMsg s) -> "
        , fmtType thisMod "(M'.MutMsg s)" fieldType
        , " -> m ()\n"
        , case fieldLoc of
            DataField loc@DataLoc{..} -> mconcat
                [ setName, " (", fmtName thisMod typeName, " struct) value = "
                , let size = case fieldType of
                        EnumType _           -> 16
                        PrimType PrimInt{..} -> size
                        PrimType PrimFloat32 -> 32
                        PrimType PrimFloat64 -> 64
                        PrimType PrimBool    -> 1
                        _ -> error $ "type " ++ show fieldType ++
                            " does not make sense in the data section!"
                  in fmtSetWordField
                        "struct"
                        ("(fromIntegral (C'.toWord value) :: Word" <> TB.fromString (show size) <> ")")
                        loc
                ]
            VoidField -> setName <> " _ = pure ()"
            PtrField idx -> mconcat
                [ setName, " (", fmtName thisMod typeName, " struct) value = "
                , "U'.setPtr (C'.toPtr value) ", TB.fromString (show idx), " struct\n"
                ]
            _ -> setName <> " _ = error " <> TB.fromString (show "TODO: generate more setters.")
        , "\n"
        , "instance (U'.ReadCtx m (M'.MutMsg s), M'.WriteCtx m s) => IsLabel "
        , TB.fromString (show fieldName), " (DC'.Set m (", fmtName thisMod typeName, " (M'.MutMsg s)) ("
        , fmtType thisMod "(M'.MutMsg s)" fieldType, ")) where\n"
        , "    fromLabel = DC'.Set ", setName, "\n"
        , "\n"
        ]

fmtDecl :: Id -> (Name, Decl) -> TB.Builder
fmtDecl thisMod (name, DeclDef d)   = fmtDataDef thisMod name d
fmtDecl thisMod (name, DeclConst WordConst{wordType,wordValue}) =
    let nameText = fmtName thisMod (valueName name)
    in mconcat
        [ nameText, " :: ", fmtType thisMod "msg" wordType, "\n"
        , nameText, " = C'.fromWord ", TB.fromString (show wordValue), "\n"
        ]

fmtDataDef :: Id -> Name -> DataDef -> TB.Builder
fmtDataDef thisMod dataName DataDef{dataVariants=[Variant{..}], dataCerialType=CTyStruct, ..} =
    fmtNewtypeStruct thisMod dataName <>
    case variantParams of
        Record fields ->
            mintercalate "\n" $ map (fmtFieldAccessor thisMod dataName variantName) fields
        _ -> ""
fmtDataDef thisMod dataName DataDef{dataCerialType=CTyStruct,dataTagLoc=Just tagLoc,dataVariants} =
    let nameText = fmtName thisMod dataName
    in mconcat
        [ "data ", nameText, " msg"
        , "\n    = "
        , mintercalate "\n    | " (map fmtDataVariant dataVariants)
        , "\n"
        -- Generate auxiliary newtype definitions for group fields:
        , mintercalate "\n" (map fmtVariantAuxNewtype dataVariants)
        , "\ninstance C'.IsStruct msg (", nameText, " msg) where"
        , "\n    fromStruct struct = do"
        , "\n        tag <- ", fmtGetWordField "struct" tagLoc
        , "\n        case tag of"
        , mconcat $ map fmtVariantCase $ sortVariants dataVariants
        , "\n"
        , fmtStructListElem nameText
        , "\ninstance C'.IsPtr msg (", nameText, " msg) where"
        , "\n    fromPtr msg ptr = C'.fromPtr msg ptr >>= ", fmtRestrictedFromStruct nameText, "\n"
        , "\n    toPtr = error \"TODO: toPtr for non-newtype structs.\"\n"
        , "\n"
        , fmtStructListIsPtr nameText
        ]
  where
    fmtDataVariant Variant{..} = fmtName thisMod variantName <>
        case variantParams of
            Record _   -> " (" <> fmtName thisMod (subName variantName "group' msg)")
            NoParams   -> ""
            Unnamed ty _ -> " " <> fmtType thisMod "msg" ty
    fmtVariantCase Variant{..} =
        let nameText = fmtName thisMod variantName
        in "\n            " <>
            case variantTag of
                Just tag ->
                    mconcat
                        [ TB.fromString (show tag), " -> "
                        , case variantParams of
                            Record _  -> nameText <> " <$> C'.fromStruct struct"
                            NoParams  -> "pure " <> nameText
                            Unnamed _ HereField -> nameText <> " <$> C'.fromStruct struct"
                            Unnamed _ VoidField -> error
                                "Shouldn't happen; this should be NoParams."
                                -- TODO: rule this out statically if possible.
                            Unnamed _ (DataField loc) ->
                                nameText <> " <$> " <> fmtGetWordField "struct" loc
                            Unnamed _ (PtrField idx) -> mconcat
                                [ nameText <> " <$> "
                                , " (U'.getPtr ", TB.fromString (show idx), " struct"
                                , " >>= C'.fromPtr (U'.message struct))"
                                ]
                        ]
                Nothing ->
                    "_ -> pure $ " <> nameText <> " tag"
    fmtVariantAuxNewtype Variant{variantName, variantParams=Record fields} =
        let typeName = subName variantName "group'"
        in fmtNewtypeStruct thisMod typeName <>
            mintercalate "\n" (map (fmtFieldAccessor thisMod typeName variantName) fields)
    fmtVariantAuxNewtype _ = ""
fmtDataDef thisMod dataName DataDef{dataCerialType=CTyEnum,..} =
    let typeName = fmtName thisMod dataName
    in mconcat
        [ "data ", typeName
        , "\n    = "
        , mintercalate "\n    | " (map fmtEnumVariant dataVariants)
        , "\n"
        -- Generate an Enum instance. This is a trivial wrapper around the
        -- IsWord instance, below.
        , "instance Enum ", typeName, " where\n"
        , "    toEnum = C'.fromWord . fromIntegral\n"
        , "    fromEnum = fromIntegral . C'.toWord\n"
        , "\n\n"
        -- Generate an IsWord instance.
        , "instance C'.IsWord ", typeName, " where"
        , "\n    fromWord n = go (fromIntegral n :: Word16)"
        , "\n      where"
        , "\n        go "
        , mintercalate "\n        go " $
            map fmtEnumFromWordCase $ sortVariants dataVariants
        , "\n    toWord "
        , mintercalate "\n    toWord " $
            map fmtEnumToWordCase   $ sortVariants dataVariants
        , "\n"
        , "instance B'.ListElem msg ", typeName, " where"
        , "\n    newtype List msg ", typeName, " = List_", typeName, " (U'.ListOf msg Word16)"
        , "\n    length (List_", typeName, " l) = U'.length l"
        , "\n    index i (List_", typeName, " l) = (C'.fromWord . fromIntegral) <$> U'.index i l"
        , "\n"
        , "instance B'.MutListElem s ", typeName, " where"
        , "\n    setIndex elt i (List_", typeName, " l) = error \"TODO: generate code for setIndex\""
        , "\n"
        , "instance C'.IsPtr msg (B'.List msg ", typeName, ") where"
        , "\n    fromPtr msg ptr = List_", typeName, " <$> C'.fromPtr msg ptr"
        , "\n    toPtr (List_", typeName, " l) = C'.toPtr l"
        , "\n"
        ]
  where
    -- | Format a data constructor in the definition of a data type for an enum.
    fmtEnumVariant Variant{variantName,variantParams=NoParams,variantTag=Just _} =
        fmtName thisMod variantName
    fmtEnumVariant Variant{variantName,variantParams=Unnamed ty _, variantTag=Nothing} =
        fmtName thisMod variantName <> " " <> fmtType thisMod "msg" ty
    fmtEnumVariant variant =
        error $ "Unexpected variant for enum: " ++ show variant
    -- | Format an equation in an enum's IsWord.fromWord implementation.
    fmtEnumFromWordCase Variant{variantTag=Just tag,variantName} =
        -- For the tags we know about:
        TB.fromString (show tag) <> " = " <> fmtName thisMod variantName
    fmtEnumFromWordCase Variant{variantTag=Nothing,variantName} =
        -- For other tags:
        "tag = " <> fmtName thisMod variantName <> " (fromIntegral tag)"
    -- | Format an equation in an enum's IsWord.toWord implementation.
    fmtEnumToWordCase Variant{variantTag=Just tag,variantName} =
        fmtName thisMod variantName <> " = " <> TB.fromString (show tag)
    fmtEnumToWordCase Variant{variantTag=Nothing,variantName} =
        "(" <> fmtName thisMod variantName <> " tag) = fromIntegral tag"
fmtDataDef _ dataName dataDef =
    error $ "Unexpected data definition: " ++ show (dataName, dataDef)

-- | @'fmtType ident msg ty@ formats the type @ty@ from module @ident@,
-- using @msg@ as the message parameter, if any.
fmtType :: Id -> TB.Builder -> Type -> TB.Builder
fmtType thisMod msg = \case
    ListOf eltType ->
        "(B'.List " <> msg <> " " <> fmtType thisMod msg eltType <> ")"
    EnumType name ->
        fmtName thisMod name
    StructType name params -> mconcat
        [ "("
        , fmtName thisMod name
        , " "
        , mintercalate " " $ msg : map (fmtType thisMod msg) params
        , ")"
        ]
    PrimType prim -> fmtPrimType msg prim
    Untyped ty -> "(Maybe " <> fmtUntyped msg ty <> ")"

fmtPrimType :: TB.Builder -> PrimType -> TB.Builder
-- TODO: most of this (except Text & Data) should probably be shared with the
-- Pure backend.
fmtPrimType _ PrimInt{isSigned=True,size}  = "Int" <> TB.fromString (show size)
fmtPrimType _ PrimInt{isSigned=False,size} = "Word" <> TB.fromString (show size)
fmtPrimType _ PrimFloat32                  = "Float"
fmtPrimType _ PrimFloat64                  = "Double"
fmtPrimType _ PrimBool                     = "Bool"
fmtPrimType _ PrimVoid                     = "()"
fmtPrimType msg PrimText                   = "(B'.Text " <> msg <> ")"
fmtPrimType msg PrimData                   = "(B'.Data " <> msg <> ")"

fmtUntyped :: TB.Builder -> Untyped -> TB.Builder
fmtUntyped msg Struct = "(U'.Struct " <> msg <> ")"
fmtUntyped msg List   = "(U'.List " <> msg <> ")"
fmtUntyped _ Cap      = "Word32"
fmtUntyped msg Ptr    = "(U'.Ptr " <> msg <> ")"

fmtName :: Id -> Name -> TB.Builder
fmtName thisMod Name{nameModule, nameLocalNS=Namespace parts, nameUnqualified=localName} =
    modPrefix <> mintercalate "'" (map TB.fromText $ parts <> [localName])
  where
    modPrefix = case nameModule of
        ByCapnpId id                  | id == thisMod -> ""
        FullyQualified (Namespace []) -> ""
        _                             -> fmtModRef nameModule <> "."
