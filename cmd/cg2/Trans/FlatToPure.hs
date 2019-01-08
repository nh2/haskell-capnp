{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
module Trans.FlatToPure where

import qualified IR.Common as C
import qualified IR.Flat   as Flat
import qualified IR.Name   as Name
import qualified IR.Pure   as Pure

fileToFile :: Flat.File -> Pure.File
fileToFile Flat.File{nodes, fileId, fileName, fileImports} =
    Pure.File
        { fileId
        , fileName
        , fileImports
        , decls = concatMap nodeToDecls nodes
        , reExportEnums = concatMap nodeToReExports nodes
        }

nodeToReExports :: Flat.Node -> [Name.LocalQ]
nodeToReExports Flat.Node{name=Name.CapnpQ{local}, union_=Flat.Enum _} = [ local ]
nodeToReExports _ = []

nodeToDecls :: Flat.Node -> [Pure.Decl]
nodeToDecls Flat.Node{name=name@Name.CapnpQ{local}, nodeId, union_} = case union_ of
    Flat.Enum _ -> [] -- TODO
    Flat.Interface{} -> [] -- TODO
    Flat.Struct{fields=[], union=Just Flat.Union{variants}} ->
        -- It's just one big union; skip the outer struct wrapper and make it
        -- a top-level sum type.
        [ Pure.Data
            { typeName = local
            , variants =
                [ Pure.Variant
                    { name = variantName
                    , arg = case fieldLocType of
                        C.VoidField ->
                            -- If the argument is void, just have no argument.
                            Pure.None
                        C.HereField
                            -- See Note [Collapsing Groups]
                            (C.StructType
                                Flat.Node
                                    { union_=Flat.Struct
                                        { isGroup=True
                                        , union=Nothing
                                        , fields
                                        }
                                    }) ->
                                    Pure.Record (map fieldToField fields)
                        _ ->
                            Pure.Positional (Pure.type_ (fieldToField field))
                    }
                | Flat.Variant
                    { field=field@Flat.Field
                        { fieldName=Name.CapnpQ{local=variantName}
                        , fieldLocType
                        }
                    } <- variants
                ]
            , isUnion = True
            }
        ]
    Flat.Struct{ isGroup=True, union=Nothing } -> [] -- See Note [Collapsing Groups]
    Flat.Struct{ fields, union, dataWordCount, pointerCount } ->
        Pure.Data
            { typeName = local
            , variants =
                [ Pure.Variant
                    { name = local
                    , arg = Pure.Record $
                        map fieldToField fields
                        ++ case union of
                            Nothing ->
                                []
                            Just _ ->
                                [ Pure.Field
                                    { name = "union'"
                                    , type_ = C.CompositeType $ C.StructType $ Name.mkSub name ""
                                    }
                                ]
                    }
                ]
            , isUnion = False
            }
        : case union of
            Just _ ->
                -- Now make a version that's just the union.
                nodeToDecls Flat.Node
                    { name = Name.mkSub name ""
                    , nodeId
                    , union_ = Flat.Struct
                        { fields = []
                        , isGroup = True
                        , dataWordCount
                        , pointerCount
                        , union = union
                        }
                    }
            Nothing ->
                []

fieldToField :: Flat.Field -> Pure.Field
fieldToField Flat.Field{fieldName, fieldLocType} = Pure.Field
    { name = Name.getUnQ fieldName
    , type_ = fmap
        (\Flat.Node{name} -> name)
        (C.fieldType fieldLocType)
    }

-- Note [Collapsing Groups]
-- ========================
--
-- If the argument to a union data constructor is a group, then the fields
-- never exist on their own, so it makes for a nicer API to just collapse
-- the fields directly into the variant, rather than creating an auxiliary
-- struct type.
--
-- However, this is only safe to do if the group does not itself have an
-- anonymous union. The reason for this is that otherwise we could end up
-- with two variants with a field "union'" but different types, which the
-- compiler will reject.
--
-- So the rule is, if a Field.Struct node is a group, and it does not itself
-- have an anonymous union:
--
-- 1. Don't generate a type for it.
-- 2. Collapse its fields into the data constructor for the union.
--
-- Note that we actually depend on (1) to avoid name collisions, since
-- otherwise both the data constructor for the anonymous union and the
-- data constructor for the group will be the same.
