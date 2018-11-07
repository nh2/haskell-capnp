{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
-- Generate idiomatic haskell data types from the types in IR.
module Backends.Pure
    ( fmtModule
    ) where

import Data.String                  (fromString)
import GHC.Exts                     (IsList(..))
import Text.PrettyPrint.Leijen.Text (hcat, vcat)
import Text.Printf                  (printf)

import qualified Data.Map.Strict              as M
import qualified Data.Text                    as T
import qualified Text.PrettyPrint.Leijen.Text as PP

import Backends.Common
import Fmt
import IR
import Util

-- | If a module reference refers to a generated module, does it
-- refer to the raw, low-level module or the *.Pure variant (which
-- this module generates)?
data ModRefType = Pure | Raw
    deriving(Show, Read, Eq)

fmtName :: ModRefType -> Id -> Name -> PP.Doc
fmtName refTy thisMod Name{..} = modPrefix <> localName
  where
    localName = mintercalate "'" $
        map PP.textStrict $ fromList $ toList nameLocalNS ++ [nameUnqualified]
    modPrefix
        | null nsParts = ""
        | refTy == Pure && modRefToNS refTy (ByCapnpId thisMod) == ns = ""
        | otherwise = fmtModRef refTy nameModule <> "."
    ns@(Namespace nsParts) = modRefToNS refTy nameModule

modRefToNS :: ModRefType -> ModuleRef -> Namespace
modRefToNS _ (FullyQualified ns) = ns
modRefToNS ty (ByCapnpId id) = Namespace $ case ty of
    Pure -> ["Capnp", "Gen", "ById", T.pack (printf "X%x" id), "Pure"]
    Raw  -> ["Capnp", "Gen", "ById", T.pack (printf "X%x" id)]


fmtModule :: Module -> [(FilePath, PP.Doc)]
fmtModule mod@Module{modName=Namespace modNameParts,..} =
    [ ( T.unpack $ mintercalate "/" humanParts <> ".hs"
      , mainContent
      )
    , ( printf "Capnp/Gen/ById/X%x/Pure.hs" modId
      , vcat
            [ "{-# OPTIONS_GHC -Wno-unused-imports #-}"
            , "{- |"
            , hcat [ "Module: ", machineMod ]
            , hcat [ "Description: Machine-addressable alias for '", humanMod, "'." ]
            , "-}"
            , hcat [ "module ", machineMod, "(module ", humanMod, ") where" ]
            , ""
            , hcat [ "import ", humanMod ]
            ]
      )
    ]
 where
  machineMod = fmtModRef Pure (ByCapnpId modId)
  humanMod = fmtModRef Pure $ FullyQualified $ Namespace humanParts
  humanParts = "Capnp":"Gen":modNameParts ++ ["Pure"]
  modFileText = PP.textStrict modFile
  mainContent = vcat
    [ "{-# LANGUAGE DuplicateRecordFields #-}"
    , "{-# LANGUAGE RecordWildCards #-}"
    , "{-# LANGUAGE FlexibleInstances #-}"
    , "{-# LANGUAGE FlexibleContexts #-}"
    , "{-# LANGUAGE MultiParamTypeClasses #-}"
    , "{-# LANGUAGE ScopedTypeVariables #-}"
    , "{-# LANGUAGE TypeFamilies #-}"
    , "{-# LANGUAGE DeriveGeneric #-}"
    , "{-# LANGUAGE OverloadedStrings #-}"
    -- Some of these warnings can crop up in the generated code, and this is
    -- expected so we disable them via a pragma:

    -- Some of the modules we import may not be used if the original schema
    -- did not include the construct we need them for. This is OK:
    , "{-# OPTIONS_GHC -Wno-unused-imports #-}"

    -- The pure modules define some instances for types defined in the raw
    -- modules. Arguably this warning should happen at the package level
    -- anyway:
    , "{-# OPTIONS_GHC -Wno-orphans #-}"

    -- Parts of the generated code deliberately use name shadowing:
    , "{-# OPTIONS_GHC -Wno-name-shadowing #-}"

    -- This happens with empty structs, which bind the struct to a variable
    -- but don't actually need to extract any info from it. This is most
    -- common for the parameter or result structs for a method:
    , "{-# OPTIONS_GHC -Wno-unused-matches #-}"
    , "{- |"
    , "Module: " <> humanMod
    , "Description: " <> "High-level generated module for " <> modFileText
    , ""
    , "This module is the generated code for " <> modFileText <> ","
    , "for the high-level api."
    , "-}"
    , "module " <> humanMod <> " (" <> fmtExportList mod, ") where"
    , ""
    , "-- Code generated by capnpc-haskell. DO NOT EDIT."
    , "-- Generated from schema file: " <> modFileText
    , ""
    , "import Data.Int"
    , "import Data.Word"
    , ""
    , "import Data.Default (Default(def))"
    , "import GHC.Generics (Generic)"
    , ""
    , "import Capnp.Basics.Pure (Data, Text)"
    , "import Control.Monad.Catch (MonadThrow(throwM))"
    , "import Control.Concurrent.STM (atomically)"
    , "import Control.Monad.IO.Class (liftIO)"
    , "import Capnp.TraversalLimit (MonadLimit, evalLimitT)"
    , ""
    , "import Control.Monad (forM_)"
    , ""
    , "import qualified Capnp.Convert as Convert"
    , "import qualified Capnp.Message as M'"
    , "import qualified Capnp.Untyped as U'"
    , "import qualified Capnp.Untyped.Pure as PU'"
    , "import qualified Capnp.GenHelpers.Pure as PH'"
    , "import qualified Capnp.Classes as C'"
    -- We need to do this conditionally to avoid a circular dependency
    -- between the rpc system and the generated code for rpc.capnp:
    , if hasInterfaces mod then
        vcat
        [ "import qualified Capnp.Rpc as Rpc"
        , "import qualified Capnp.Gen.Capnp.Rpc.Pure as Rpc"
        , "import qualified Capnp.GenHelpers.Rpc as RH'"
        ]
      else
        ""
    , ""
    , "import qualified Data.Vector as V"
    , "import qualified Data.ByteString as BS"
    , ""
    , fmtImport Raw $ Import (ByCapnpId modId)
    , vcat $ map (fmtImport Pure) modImports
    , vcat $ map (fmtImport Raw) modImports
    , ""
    , vcat $ map (fmtDecl modId) (M.toList modDecls)
    ]

fmtExportList :: Module -> PP.Doc
fmtExportList Module{modId,modDecls} =
    mintercalate ", " (map (fmtExport modId) (M.toList modDecls))

fmtExport :: Id -> (Name, Decl) -> PP.Doc
fmtExport thisMod (name, DeclDef DefStruct{}) =
    fmtName Pure thisMod name <> "(..)"
fmtExport thisMod (name, DeclDef DefUnion{}) =
    fmtName Pure thisMod name <> "(..)"
fmtExport thisMod (name, DeclDef (DefInterface _)) = mconcat
    [ fmtName Pure thisMod name, "(..), "
    , fmtName Pure thisMod name, "'server_(..),"
    , "export_", fmtName Pure thisMod name
    ]
-- These are 'Raw' because we're just re-exporting them:
fmtExport thisMod (name, DeclDef DefEnum{}) =
    fmtName Raw thisMod name <> "(..)"
fmtExport thisMod (name, DeclConst VoidConst) =
    fmtName Raw thisMod (valueName name)
fmtExport thisMod (name, DeclConst WordConst{}) =
    fmtName Raw thisMod (valueName name)

fmtExport thisMod (name, DeclConst _) =
    fmtName Pure thisMod (valueName name)

fmtImport :: ModRefType -> Import -> PP.Doc
fmtImport ty (Import ref) = "import qualified " <> fmtModRef ty ref

fmtModRef :: ModRefType -> ModuleRef -> PP.Doc
fmtModRef ty ref = mintercalate "." (map PP.textStrict $ toList $ modRefToNS ty ref)

fmtType :: Id -> Type -> PP.Doc
fmtType thisMod (CompositeType (StructType name params)) =
    fmtName Pure thisMod name
    <> hcat [" (" <> fmtType thisMod ty <> ")" | ty <- params]
fmtType thisMod (WordType (EnumType name)) = fmtName Raw thisMod name
fmtType thisMod (PtrType (ListOf eltType)) = "PU'.ListOf (" <> fmtType thisMod eltType <> ")"
fmtType thisMod (PtrType (PtrComposite ty)) = fmtType thisMod (CompositeType ty)
fmtType thisMod (PtrType (PtrInterface name)) = fmtName Pure thisMod name
fmtType _ VoidType = "()"
fmtType _ (WordType (PrimWord prim)) = fmtPrimWord prim
fmtType _ (PtrType (PrimPtr PrimText)) = "Text"
fmtType _ (PtrType (PrimPtr PrimData)) = "Data"
fmtType _ (PtrType (PrimPtr (PrimAnyPtr ty))) = "Maybe (" <> fmtAnyPtr ty <> ")"

fmtAnyPtr :: AnyPtr -> PP.Doc
fmtAnyPtr Struct = "PU'.Struct"
fmtAnyPtr List   = "PU'.List"
fmtAnyPtr Cap    = "PU'.Cap"
fmtAnyPtr Ptr    = "PU'.PtrType"

fmtVariant :: Id -> Variant -> PP.Doc
fmtVariant thisMod Variant{variantName,variantParams} =
    fmtName Pure thisMod variantName
    <> case variantParams of
        Unnamed VoidType _ -> ""
        Unnamed ty _ -> " (" <> fmtType thisMod ty <> ")"
        Record [] -> ""
        Record fields -> PP.line <> indent
            (PP.braces $ vcat $
                PP.punctuate "," $ map (fmtField thisMod) fields)

fmtField :: Id -> Field -> PP.Doc
fmtField thisMod Field{fieldName,fieldLocType} =
    PP.textStrict fieldName <> " :: " <> fmtType thisMod fieldType
  where
    fieldType = case fieldLocType of
        VoidField      -> VoidType
        DataField _ ty -> WordType ty
        PtrField _ ty  -> PtrType ty
        HereField ty   -> CompositeType ty

fmtDecl :: Id -> (Name, Decl) -> PP.Doc
fmtDecl thisMod (name, DeclDef d)   = fmtDataDef thisMod name d
fmtDecl thisMod (name, DeclConst c) = fmtConst thisMod name c

-- | Format a constant declaration.
fmtConst :: Id -> Name -> Const -> PP.Doc
fmtConst thisMod name value =
    let pureName = fmtName Pure thisMod (valueName name)
        rawName = fmtName Raw thisMod (valueName name)
    in case value of
        -- For word types, We just re-export the definitions from the
        -- low-level module, so we don't need to declare anything here:
        VoidConst -> ""
        WordConst{} -> ""

        PtrConst{ptrType} -> vcat
            [ hcat [ pureName, " :: ", fmtType thisMod (PtrType ptrType) ]
            , hcat [ pureName, " = PH'.toPurePtrConst ", rawName ]
            ]

fmtDataDef :: Id -> Name -> DataDef -> PP.Doc
fmtDataDef thisMod dataName DefEnum{} =
    -- We re-use the same datatype from the raw module, so we just need
    -- to declare a trivial instance.
    let rawName = fmtName Raw thisMod dataName
    in vcat
    [ instance_ [] ("C'.Decerialize " <> rawName)
        [ hcat [ "type Cerial msg ", rawName, " = ", rawName ]
        , hcat [ "decerialize = pure" ]
        ]
    ]
fmtDataDef thisMod dataName (DefInterface InterfaceDef{interfaceId, methods}) =
    let pureName = fmtName Pure thisMod dataName
        rawName  = fmtName Raw  thisMod dataName
        pureValName name = fmtName Pure thisMod (valueName name)
    in vcat
    [ hcat [ "newtype ", pureName, " = ", pureName, " M'.Client" ]
    , "    deriving(Show, Eq, Read, Generic)"
    , instance_ [] ("Rpc.IsClient " <> pureName)
        [ hcat [ "fromClient = ", pureName ]
        , hcat [ "toClient (", pureName, " client) = client" ]
        ]
    , instance_ [] ("C'.FromPtr msg " <> pureName)
        [ "fromPtr = RH'.isClientFromPtr" ]
    , instance_ [] ("C'.ToPtr s " <> pureName)
        [ "toPtr = RH'.isClientToPtr" ]
    , instance_ [] ("C'.Decerialize " <> pureName)
        [ hcat [ "type Cerial msg ", pureName, " = ", rawName, " msg" ]
        , hcat [ "decerialize (", rawName, " Nothing) = pure $ ", pureName, " M'.nullClient" ]
        , hcat [ "decerialize (", rawName, " (Just cap)) = ", pureName, " <$> U'.getClient cap" ]
        ]
    , instance_ [] ("C'.Cerialize s " <> pureName)
        [ hcat [ "cerialize msg (", pureName, " client) = ", rawName, " . Just <$> U'.appendCap msg client" ]
        ]
    , class_ [] (pureName <> "'server_ cap")
        [ hcat
            -- We provide default definitions for all methods that just throw
            -- 'unimplemented', so that if a schema adds new methods, the code
            -- will still compile and behave the same. But we add a MINIMAL
            -- pragma so the user will still get a *warning* if they forget
            -- a method.
            [ "{-# MINIMAL "
            , hcat $ PP.punctuate ", " $ map
                (\Method{methodName} -> pureValName methodName)
                methods
            , " #-}"
            ]
        , vcat $ flip map methods $ \Method{..} -> vcat
            [ hcat
                [ pureValName methodName
                , " :: "
                , fmtType thisMod (CompositeType paramType)
                , " -> cap -> Rpc.RpcT IO ("
                , fmtType thisMod (CompositeType resultType)
                , ")"
                ]
            , hcat [ pureValName methodName, " _ _ = Rpc.throwMethodUnimplemented" ]
            ]
        ]
    , hcat [ "export_", pureName, " :: ", pureName, "'server_ a => a -> Rpc.RpcT IO ", pureName ]
    , hcat [ "export_", pureName, " server_ = ", pureName, " <$> Rpc.export Rpc.Server" ]
    , indent $ vcat
        [ "{ handleStop = pure () -- TODO"
        , ", handleCall = \\interfaceId methodId payload fulfiller -> case interfaceId of"
        , indent $ vcat
            -- TODO: superclasses.
            [ hcat [ fromString (show interfaceId), " -> case methodId of" ]
            , indent $ vcat
                [ vcat $ flip map methods $ \Method{..} -> vcat
                    [ hcat [ fromString (show ordinal), " -> do" ]
                    , indent $ vcat
                        [ hcat [ "RH'.handleMethod server_ ", pureValName methodName, " payload fulfiller" ] ]
                        -- TODO:
                        --
                        -- * handle exceptions
                    ]
                , "_ -> liftIO $ atomically $ Rpc.breakPromise fulfiller Rpc.methodUnimplemented"
                ]
            , "_ -> liftIO $ atomically $ Rpc.breakPromise fulfiller Rpc.methodUnimplemented"
            ]
        , "}"
        ]
    , instance_ [] (pureName <> "'server_ " <> pureName)
        $ flip map methods $ \Method{..} -> vcat
            [ hcat [ pureValName methodName,  " args (", pureName, " client) = do" ]
            , indent $ vcat
                -- we're using maxBound as the traversal limit below. This is OK
                -- because we're only touching values converted from already-validated
                -- high-level api types that we serailize ourselves, so they can't
                -- be malicious in the ways that the traversal limit is designed to
                -- mitiage
                [ "args' <- PH'.createPure maxBound $ Convert.valueToMsg args >>= PH'.getRoot"
                , hcat
                    [ "resultPromise <- Rpc.call "
                    , PP.textStrict $ T.pack $ show interfaceId
                    , " "
                    , PP.textStrict $ T.pack $ show ordinal
                    , " (Just (U'.PtrStruct args'))"
                    , " client"
                    ]
                , "result <- Rpc.waitIO resultPromise"
                , "evalLimitT maxBound $ PH'.convertValue result"
                ]
            ]
    ]
fmtDataDef thisMod dataName dataDef =
    let rawName = fmtName Raw thisMod dataName
        pureName = fmtName Pure thisMod dataName

        unknownName = subName dataName "unknown'"
    in vcat
        [ case dataDef of
            -- TODO: refactor so we don't need these cases.
            DefEnum{} ->
                -- TODO: refactor so we don't need this case.
                error "BUG: this should have been ruled out above."
            DefInterface _ ->
                error "BUG: this should have been ruled out above."
            DefStruct StructDef{fields,info} ->
                let dataVariant =
                        -- TODO: some of the functions we use still expect structs
                        -- to just be single-variant unions; this is a stand-in,
                        -- but we should update those at some point.
                        Variant
                            { variantName = dataName
                            , variantParams = Record fields
                            , variantTag = 0 -- doesn't matter; just formatting
                                             -- the data constructor, so this
                                             -- isn't used.
                            }
                in vcat
                [ data_ (fmtName Pure thisMod dataName)
                    [ fmtVariant thisMod dataVariant ]
                    ["Show", "Read", "Eq", "Generic"]
                , instance_ [] ("C'.Decerialize " <> pureName)
                    [ hcat [ "type Cerial msg ", pureName, " = ", rawName, " msg" ]
                    , "decerialize raw = do"
                    , indent $ fmtDecerializeArgs dataName fields
                    ]
                , instance_ [] ("C'.Marshal " <> pureName)
                    [ "marshalInto raw value = do"
                    , indent $ vcat
                        [ "case value of\n"
                        , indent $ vcat
                            [ fmtCerializeVariant False dataVariant ]
                        ]
                    ]
                , case info of
                    IsStandalone{} ->
                        instance_ [] ("C'.Cerialize s " <> pureName)
                            []
                    _ ->
                        ""
                ]
            DefUnion{dataVariants,parentStructName,parentStruct=StructDef{info}} ->
                let unknownVariantName = subName parentStructName "unknown'"
                in vcat
                [ data_
                    (fmtName Pure thisMod dataName)
                    (map (fmtVariant thisMod) dataVariants ++
                        [ fmtName Pure thisMod unknownVariantName <> " Word16" ]
                    )
                    ["Show", "Read", "Eq", "Generic"]
                , instance_ [] ("C'.Decerialize " <> pureName)
                    [ hcat [ "type Cerial msg ", pureName, " = ", rawName, " msg" ]
                    , "decerialize raw = do"
                    , indent $ vcat
                        [ hcat [ "raw <- ", fmtName Raw thisMod $ prefixName "get_" (subName dataName ""), " raw" ]
                        , "case raw of"
                        , indent $ vcat
                            [ vcat (map fmtDecerializeVariant dataVariants)
                            , hcat
                                [ fmtName Raw thisMod unknownName, " val -> pure $ "
                                , fmtName Pure thisMod unknownVariantName, " val"
                                ]
                            ]
                        ]
                    ]
                , instance_ [] ("C'.Marshal " <> pureName)
                    [ "marshalInto raw value = do"
                    , indent $ vcat
                        [ "case value of\n"
                        , indent $ vcat
                            [ vcat $ map (fmtCerializeVariant True) dataVariants
                            , hcat
                                [ fmtName Pure thisMod unknownVariantName, " arg_ -> "
                                , fmtName Raw thisMod $ prefixName "set_" unknownName, " raw arg_"
                                ]
                            ]
                        ]
                    ]
                , case info of
                    IsStandalone{} ->
                        instance_ [] ("C'.Cerialize s " <> pureName)
                            []
                    _ ->
                        ""
                ]
        , instance_ [] ("C'.FromStruct M'.ConstMsg " <> pureName)
            [ "fromStruct struct = do"
            , indent $ vcat
                [ "raw <- C'.fromStruct struct"
                , hcat [ "C'.decerialize (raw :: ", rawName, " M'.ConstMsg)" ]
                ]
            ]
        , instance_ [] ("Default " <> pureName)
            [ "def = PH'.defaultStruct"
            ]

        ]
  where
    fmtDecerializeArgs variantName [] =
        hcat [ "pure $ ", fmtName Pure thisMod variantName ]
    fmtDecerializeArgs variantName fields = vcat
        [ hcat [ fmtName Pure thisMod variantName, " <$>" ]
        , indent $ vcat $ PP.punctuate " <*>" $
            flip map fields $ \Field{fieldName,fieldLocType} -> hcat
                [ "(", fmtName Raw thisMod $ prefixName "get_" (subName variantName fieldName)
                , " raw", case fieldLocType of
                    -- Data and void fields are always the same type in Raw and Pure forms,
                    -- so we don't need to convert them.
                    DataField _ _ -> ""
                    VoidField     -> ""
                    _             -> " >>= C'.decerialize"
                , ")"
                ]
        ]
    fmtDecerializeVariant Variant{variantName,variantParams} =
        fmtName Raw thisMod variantName <>
        case variantParams of
            Unnamed VoidType _ -> " -> pure " <> fmtName Pure thisMod variantName
            Record []          -> " -> pure " <> fmtName Pure thisMod variantName
            Record fields ->
              " raw -> " <> fmtDecerializeArgs variantName fields
            Unnamed (WordType _) _ -> hcat
                [ " val -> pure (", fmtName Pure thisMod variantName, " val)" ]
            _ -> hcat
                [ " val -> ", fmtName Pure thisMod variantName, " <$> C'.decerialize val" ]
    fmtCerializeVariant isUnion Variant{variantName, variantParams} =
        fmtName Pure thisMod variantName <>
        let accessorName prefix = fmtName Raw thisMod (prefixName prefix variantName)
            setterName = accessorName "set_"
        in case variantParams of
            Unnamed VoidType VoidField ->
                hcat [ " -> ", setterName, " raw" ]
            Unnamed _ (DataField _ _) ->
                hcat [ " arg_ -> ", setterName, " raw arg_"]
            Unnamed (WordType _) VoidField ->
                -- TODO: this is the unknown variant. We should find a better
                -- way to represent this; the structure of the IR here is sloppy
                -- work.
                hcat [ " arg_ -> ", setterName, " raw arg_" ]
            Unnamed _ fieldLocType -> vcat
                [ " arg_ -> do"
                , indent (fmtUseAccessors accessorName "arg_" fieldLocType)
                ]
            Record [] -> " -> pure ()"
            Record fields -> vcat
                [ "{..} -> do"
                , indent $ vcat
                    [ if isUnion
                        then "raw <- " <> setterName <> " raw"
                        else ""
                    , vcat (map (fmtCerializeField variantName) fields)
                    ]
                ]
    fmtCerializeField variantName Field{fieldName,fieldLocType} =
        let accessorName prefix = fmtName Raw thisMod $ prefixName prefix (subName variantName fieldName)
        in fmtUseAccessors accessorName fieldName fieldLocType
    fmtUseAccessors accessorName fieldVarName fieldLocType =
        let setterName = accessorName "set_"
            getterName = accessorName "get_"
            newName = accessorName "new_"
            fieldNameText = PP.textStrict fieldVarName
        in case fieldLocType of
            DataField _ _ -> hcat [ setterName, " raw ", fieldNameText ]
            VoidField -> hcat [ setterName, " raw" ]
            HereField _ -> vcat
                [ hcat [ "field_ <- ", getterName, " raw" ]
                , hcat [ "C'.marshalInto field_ ", fieldNameText ]
                ]
            PtrField _ ty -> case ty of
                PtrInterface _ -> vcat
                    [ hcat [ "field_ <- C'.cerialize (U'.message raw) ", fieldNameText ]
                    , hcat [ setterName, " raw field_" ]
                    ]
                PrimPtr PrimData -> vcat
                    [ hcat [ "field_ <- ", newName, " (BS.length ", fieldNameText, ") raw" ]
                    , hcat [ "C'.marshalInto field_ ", fieldNameText ]
                    ]
                PrimPtr PrimText -> vcat
                    [ hcat [ "field_ <- C'.cerialize (U'.message raw) ", fieldNameText ]
                    , hcat [ setterName, " raw field_" ]
                    ]
                PrimPtr (PrimAnyPtr _) -> vcat
                    [ hcat [ "field_ <- C'.cerialize (U'.message raw) ", fieldNameText ]
                    , hcat [ setterName, " raw field_" ]
                    ]
                ListOf eltType -> vcat
                    [ hcat [ "let len_ = V.length ", fieldNameText ]
                    , hcat [ "field_ <- ", newName, " len_ raw" ]
                    , case eltType of
                        VoidType ->
                            ""
                        CompositeType (StructType _ _) -> vcat
                            [ "forM_ [0..len_ - 1] $ \\i -> do"
                            , indent $ vcat
                                [ "elt <- C'.index i field_"
                                , hcat [ "C'.marshalInto elt (", fieldNameText, " V.! i)" ]
                                ]
                            ]
                        WordType _ -> vcat
                            [ "forM_ [0..len_ - 1] $ \\i -> do"
                            , indent $ vcat
                                [ hcat [ "C'.setIndex (", fieldNameText, " V.! i) i field_" ] ]
                            ]
                        PtrType _ ->
                            "pure ()" -- TODO
                    ]
                PtrComposite _ -> vcat
                    [ hcat [ "field_ <- ", newName, " raw" ]
                    , hcat [ "C'.marshalInto field_ ", fieldNameText ]
                    ]
