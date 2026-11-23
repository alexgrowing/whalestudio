// Lean compiler output
// Module: Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.AlgebraicWeights.IsAlgWeight
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lp_mathlib_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Topology___aux__Mathlib__Topology__Baire__BaireMeasurable______delab__app__Topology__term_u2200_u1d47___x2c____1_spec__0___redArg(lean_object*);
lean_object* lp_mathlib_Mathlib_Notation3_matchExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isType0___boxed(lean_object*);
lean_object* lp_mathlib_Mathlib_Notation3_matchFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Mathlib_Notation3_matchApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Mathlib_Notation3_MatchState_empty;
lean_object* lp_mathlib_Mathlib_Notation3_matchApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Mathlib_Notation3_withHeadRefIfTagAppFns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withOverApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Int_instAddMonoid;
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Units_instMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_zpowersHom___redArg(lean_object*);
lean_object* lp_mathlib_MonoidHom_toAdditiveRight___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_lift___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoidHom_toMultiplicativeLeft(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPExplicit___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_instOne___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transvection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_SpecialLinearGroup_toGL___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_mulSingle___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPNotation___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_Uup(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_Uup___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tvAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tvAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tvAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_NX_charOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NX_charOf___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__0_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__1_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Formalism"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__2_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__1_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 157, 133, 115, 178, 168, 218, 108)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__3 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__3_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LocalToGlobal"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__4 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__4_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__3_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__4_value),LEAN_SCALAR_PTR_LITERAL(238, 135, 31, 149, 215, 126, 90, 251)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__5 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__5_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NormalizedHeckeFactors"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__6 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__6_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__5_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__6_value),LEAN_SCALAR_PTR_LITERAL(149, 131, 6, 63, 161, 61, 86, 239)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__7 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__7_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ExpDefs"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__8 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__8_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__7_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 25, 111, 88, 141, 122, 164, 58)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__9 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__9_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(119, 130, 36, 115, 34, 29, 166, 10)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__10 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__10_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__10_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 160, 39, 7, 0, 143, 91, 98)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__11 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__11_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "L2"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__12 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__12_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__11_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__12_value),LEAN_SCALAR_PTR_LITERAL(251, 69, 56, 158, 69, 0, 34, 113)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__13 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__13_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "NX"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__14 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__14_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__13_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__14_value),LEAN_SCALAR_PTR_LITERAL(11, 152, 160, 119, 59, 145, 219, 24)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__15 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__15_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "termL⁺"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__16 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__16_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__15_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__16_value),LEAN_SCALAR_PTR_LITERAL(212, 38, 212, 8, 25, 151, 169, 78)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__17 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__17_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "L⁺"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__18 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__18_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__18_value)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__19 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__19_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__17_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__19_value)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__20 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__20_value;
LEAN_EXPORT const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__20_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value_aux_0),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value_aux_1),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value_aux_2),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "NumberField.maximalRealSubfield"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5_value;
static lean_once_cell_t lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NumberField"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "maximalRealSubfield"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__8 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__8_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(55, 203, 65, 122, 201, 69, 101, 228)}};
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9_value_aux_0),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(18, 34, 94, 81, 114, 207, 252, 32)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__10 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__10_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__11 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__11_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__12 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__12_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__13 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__13_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "L"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__14 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__14_value;
static lean_once_cell_t lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(177, 109, 157, 99, 170, 114, 243, 148)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__16 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__16_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(177, 109, 157, 99, 170, 114, 243, 148)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__17 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__17_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__18 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__18_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__17_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(28, 228, 238, 215, 143, 34, 241, 112)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__19 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__19_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__19_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 67, 2, 198, 28, 18, 242, 252)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__20 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__20_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__20_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 163, 27, 59, 232, 3, 92, 245)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__21 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__21_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__21_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__6_value),LEAN_SCALAR_PTR_LITERAL(242, 106, 185, 58, 128, 46, 30, 38)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__22 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__22_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__22_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__8_value),LEAN_SCALAR_PTR_LITERAL(69, 238, 60, 53, 170, 119, 195, 109)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__23 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__23_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__23_value),((lean_object*)(((size_t)(1828718905) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(238, 16, 186, 186, 90, 224, 170, 12)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__24 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__24_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__25 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__25_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__24_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(121, 228, 183, 41, 84, 48, 7, 254)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__26 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__26_value;
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__27 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__27_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__26_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(49, 216, 219, 49, 36, 91, 25, 64)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__28 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__28_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__28_value),((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(224, 195, 127, 126, 248, 181, 64, 130)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__29 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__29_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__30 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__30_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__31 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__31_value;
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isType0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__0_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Mathlib_Notation3_matchExpr___boxed, .m_arity = 9, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__0_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__1_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Mathlib_Notation3_matchFVar___boxed, .m_arity = 10, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__16_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__1_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__2_value;
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__2___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___boxed, .m_arity = 10, .m_num_fixed = 3, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__2_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPNotation___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPExplicit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_withOverApp___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__3_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7_value;
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_TypeSpF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_TypeSpF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "termL⁺_1"};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__0_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__15_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 232, 40, 220, 28, 140, 121, 4)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__1_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__19_value)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__2_value;
LEAN_EXPORT const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__2_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__23_value),((lean_object*)(((size_t)(1917484068) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 248, 120, 32, 145, 0, 66, 62)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(206, 96, 11, 211, 42, 42, 177, 201)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(162, 120, 132, 47, 54, 110, 239, 210)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2_value),((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(111, 196, 163, 248, 125, 62, 208, 15)}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__4 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__4_value;
static const lean_ctor_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__5 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__5_value;
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___lam__2___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___boxed, .m_arity = 10, .m_num_fixed = 3, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__0_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__1_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__0_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_withOverApp___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__1_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2_value;
static const lean_closure_object lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5_value),((lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__2_value)} };
static const lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3 = (const lean_object*)&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3_value;
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_NX_detT___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_NX_detT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NX_detT___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_NX_detT___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_NX_detT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_NX_detT___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NX_detT___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_NX_detT___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_NX_topR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_NX_topR___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NX_topR___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_NX_topR___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_Uup(lean_object* v_00_u03b9_1_, lean_object* v_p_2_, lean_object* v_r_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_Uup___boxed(lean_object* v_00_u03b9_5_, lean_object* v_p_6_, lean_object* v_r_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_L2_NX_Uup(v_00_u03b9_5_, v_p_6_, v_r_7_);
lean_dec(v_r_7_);
lean_dec_ref(v_p_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg___lam__0(lean_object* v_a_9_, lean_object* v_toSemiring_10_, lean_object* v_M_11_, lean_object* v_b_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_add(v_a_9_, v___x_13_);
v___x_15_ = lean_nat_dec_eq(v_b_12_, v___x_14_);
lean_dec(v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v_toZero_17_; 
lean_dec(v_b_12_);
lean_dec(v_M_11_);
lean_dec(v_a_9_);
v___x_16_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_10_);
v_toZero_17_ = lean_ctor_get(v___x_16_, 1);
lean_inc(v_toZero_17_);
lean_dec_ref(v___x_16_);
return v_toZero_17_;
}
else
{
lean_object* v___x_18_; 
lean_dec_ref(v_toSemiring_10_);
v___x_18_ = lean_apply_2(v_M_11_, v_a_9_, v_b_12_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg___lam__1(lean_object* v_toSemiring_19_, lean_object* v_M_20_, lean_object* v_toAddCommMonoid_21_, lean_object* v___x_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___x_25_; 
v___f_24_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_supSum___redArg___lam__0), 4, 3);
lean_closure_set(v___f_24_, 0, v_a_23_);
lean_closure_set(v___f_24_, 1, v_toSemiring_19_);
lean_closure_set(v___f_24_, 2, v_M_20_);
v___x_25_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_21_, v___x_22_, v___f_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg___lam__1___boxed(lean_object* v_toSemiring_26_, lean_object* v_M_27_, lean_object* v_toAddCommMonoid_28_, lean_object* v___x_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_NX_supSum___redArg___lam__1(v_toSemiring_26_, v_M_27_, v_toAddCommMonoid_28_, v___x_29_, v_a_30_);
lean_dec_ref(v_toAddCommMonoid_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum___redArg(lean_object* v_r_32_, lean_object* v_inst_33_, lean_object* v_M_34_){
_start:
{
lean_object* v_toSemiring_35_; lean_object* v_toAddCommMonoid_36_; lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_toSemiring_35_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toSemiring_35_);
lean_dec_ref(v_inst_33_);
v_toAddCommMonoid_36_ = lean_ctor_get(v_toSemiring_35_, 0);
lean_inc_ref_n(v_toAddCommMonoid_36_, 2);
v___x_37_ = l_List_finRange(v_r_32_);
lean_inc(v___x_37_);
v___f_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_supSum___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_38_, 0, v_toSemiring_35_);
lean_closure_set(v___f_38_, 1, v_M_34_);
lean_closure_set(v___f_38_, 2, v_toAddCommMonoid_36_);
lean_closure_set(v___f_38_, 3, v___x_37_);
v___x_39_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_36_, v___x_37_, v___f_38_);
lean_dec_ref(v_toAddCommMonoid_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_supSum(lean_object* v_r_40_, lean_object* v_R_41_, lean_object* v_inst_42_, lean_object* v_M_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_Formalism_L2_NX_supSum___redArg(v_r_40_, v_inst_42_, v_M_43_);
return v___x_44_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0(lean_object* v_p_46_, lean_object* v_g_47_, lean_object* v_r_48_, lean_object* v_00_u03b8_49_, lean_object* v_x_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_val_54_; lean_object* v___x_55_; lean_object* v_toFun_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc_n(v_x_50_, 2);
v___x_51_ = lean_apply_1(v_p_46_, v_x_50_);
v___x_52_ = lp_mathlib_ZMod_commRing(v___x_51_);
v___x_53_ = lean_apply_1(v_g_47_, v_x_50_);
v_val_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_val_54_);
lean_dec_ref(v___x_53_);
v___x_55_ = lean_obj_once(&lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0___closed__0);
v_toFun_56_ = lean_ctor_get(v___x_55_, 0);
v___x_57_ = lp_tree_Formalism_L2_NX_supSum___redArg(v_r_48_, v___x_52_, v_val_54_);
lean_inc(v_toFun_56_);
v___x_58_ = lean_apply_1(v_toFun_56_, v___x_57_);
v___x_59_ = lean_apply_2(v_00_u03b8_49_, v_x_50_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg(lean_object* v_inst_60_, lean_object* v_p_61_, lean_object* v_r_62_, lean_object* v_inst_63_, lean_object* v_00_u03b8_64_, lean_object* v_g_65_){
_start:
{
lean_object* v_toCommRing_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toMonoid_69_; lean_object* v___f_70_; lean_object* v___x_71_; 
v_toCommRing_66_ = lean_ctor_get(v_inst_63_, 0);
v___x_67_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_66_);
v___x_68_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_67_);
v_toMonoid_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_toMonoid_69_);
lean_dec_ref(v___x_68_);
v___f_70_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_stdVal___redArg___lam__0), 5, 4);
lean_closure_set(v___f_70_, 0, v_p_61_);
lean_closure_set(v___f_70_, 1, v_g_65_);
lean_closure_set(v___f_70_, 2, v_r_62_);
lean_closure_set(v___f_70_, 3, v_00_u03b8_64_);
v___x_71_ = lp_mathlib_Finset_prod___redArg(v_toMonoid_69_, v_inst_60_, v___f_70_);
lean_dec_ref(v_toMonoid_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___redArg___boxed(lean_object* v_inst_72_, lean_object* v_p_73_, lean_object* v_r_74_, lean_object* v_inst_75_, lean_object* v_00_u03b8_76_, lean_object* v_g_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_tree_Formalism_L2_NX_stdVal___redArg(v_inst_72_, v_p_73_, v_r_74_, v_inst_75_, v_00_u03b8_76_, v_g_77_);
lean_dec_ref(v_inst_75_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal(lean_object* v_00_u03b9_79_, lean_object* v_inst_80_, lean_object* v_p_81_, lean_object* v_r_82_, lean_object* v_K_83_, lean_object* v_inst_84_, lean_object* v_00_u03b8_85_, lean_object* v_g_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_tree_Formalism_L2_NX_stdVal___redArg(v_inst_80_, v_p_81_, v_r_82_, v_inst_84_, v_00_u03b8_85_, v_g_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_stdVal___boxed(lean_object* v_00_u03b9_88_, lean_object* v_inst_89_, lean_object* v_p_90_, lean_object* v_r_91_, lean_object* v_K_92_, lean_object* v_inst_93_, lean_object* v_00_u03b8_94_, lean_object* v_g_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_Formalism_L2_NX_stdVal(v_00_u03b9_88_, v_inst_89_, v_p_90_, v_r_91_, v_K_92_, v_inst_93_, v_00_u03b8_94_, v_g_95_);
lean_dec_ref(v_inst_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0(lean_object* v_inst_97_, lean_object* v_p_98_, lean_object* v_r_99_, lean_object* v_inst_100_, lean_object* v_00_u03b8_101_, lean_object* v_u_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_tree_Formalism_L2_NX_stdVal___redArg(v_inst_97_, v_p_98_, v_r_99_, v_inst_100_, v_00_u03b8_101_, v_u_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0___boxed(lean_object* v_inst_104_, lean_object* v_p_105_, lean_object* v_r_106_, lean_object* v_inst_107_, lean_object* v_00_u03b8_108_, lean_object* v_u_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0(v_inst_104_, v_p_105_, v_r_106_, v_inst_107_, v_00_u03b8_108_, v_u_109_);
lean_dec_ref(v_inst_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd___redArg(lean_object* v_inst_111_, lean_object* v_p_112_, lean_object* v_r_113_, lean_object* v_inst_114_, lean_object* v_00_u03b8_115_){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_116_, 0, v_inst_111_);
lean_closure_set(v___f_116_, 1, v_p_112_);
lean_closure_set(v___f_116_, 2, v_r_113_);
lean_closure_set(v___f_116_, 3, v_inst_114_);
lean_closure_set(v___f_116_, 4, v_00_u03b8_115_);
return v___f_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_psiStd(lean_object* v_00_u03b9_117_, lean_object* v_inst_118_, lean_object* v_p_119_, lean_object* v_r_120_, lean_object* v_K_121_, lean_object* v_inst_122_, lean_object* v_00_u03b8_123_){
_start:
{
lean_object* v___f_124_; 
v___f_124_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_psiStd___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_124_, 0, v_inst_118_);
lean_closure_set(v___f_124_, 1, v_p_119_);
lean_closure_set(v___f_124_, 2, v_r_120_);
lean_closure_set(v___f_124_, 3, v_inst_122_);
lean_closure_set(v___f_124_, 4, v_00_u03b8_123_);
return v___f_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tv___redArg(lean_object* v_r_125_, lean_object* v_inst_126_, lean_object* v_c_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_130_, 0, v_r_125_);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lp_mathlib_Matrix_transvection___redArg(v___x_130_, v_inst_126_, v___x_131_, v___x_132_, v_c_127_, v_a_128_, v_a_129_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tv(lean_object* v_r_134_, lean_object* v_R_135_, lean_object* v_inst_136_, lean_object* v_hr_137_, lean_object* v_c_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lp_tree_Formalism_L2_NX_tv___redArg(v_r_134_, v_inst_136_, v_c_138_, v_a_139_, v_a_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tvAt___redArg___lam__0(lean_object* v_p_142_, lean_object* v_r_143_, lean_object* v___x_144_, lean_object* v_i_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_toSemiring_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_toMonoid_151_; lean_object* v___x_152_; 
v___x_146_ = lean_apply_1(v_p_142_, v_i_145_);
v___x_147_ = lp_mathlib_ZMod_commRing(v___x_146_);
v_toSemiring_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc_ref(v_toSemiring_148_);
lean_dec_ref(v___x_147_);
v___x_149_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_149_, 0, v_r_143_);
v___x_150_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_148_, v___x_144_, v___x_149_);
v_toMonoid_151_ = lean_ctor_get(v___x_150_, 1);
lean_inc_ref(v_toMonoid_151_);
lean_dec_ref(v___x_150_);
v___x_152_ = lp_mathlib_Units_instOne___redArg(v_toMonoid_151_);
lean_dec_ref(v_toMonoid_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tvAt___redArg(lean_object* v_p_153_, lean_object* v_r_154_, lean_object* v_inst_155_, lean_object* v_x_156_, lean_object* v_j_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_toAddMonoidWithOne_161_; lean_object* v_toOne_162_; lean_object* v___x_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_inc_ref(v_p_153_);
lean_inc(v_x_156_);
v___x_158_ = lean_apply_1(v_p_153_, v_x_156_);
v___x_159_ = lp_mathlib_ZMod_commRing(v___x_158_);
lean_inc_ref_n(v___x_159_, 2);
v___x_160_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_159_);
v_toAddMonoidWithOne_161_ = lean_ctor_get(v___x_160_, 1);
lean_inc_ref(v_toAddMonoidWithOne_161_);
lean_dec_ref(v___x_160_);
v_toOne_162_ = lean_ctor_get(v_toAddMonoidWithOne_161_, 2);
lean_inc(v_toOne_162_);
lean_dec_ref(v_toAddMonoidWithOne_161_);
lean_inc_n(v_r_154_, 3);
v___x_163_ = l_List_finRange(v_r_154_);
lean_inc(v___x_163_);
v___f_164_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_tvAt___redArg___lam__0), 4, 3);
lean_closure_set(v___f_164_, 0, v_p_153_);
lean_closure_set(v___f_164_, 1, v_r_154_);
lean_closure_set(v___f_164_, 2, v___x_163_);
v___x_165_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_165_, 0, v_r_154_);
v___x_166_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_tv), 7, 5);
lean_closure_set(v___x_166_, 0, v_r_154_);
lean_closure_set(v___x_166_, 1, lean_box(0));
lean_closure_set(v___x_166_, 2, v___x_159_);
lean_closure_set(v___x_166_, 3, lean_box(0));
lean_closure_set(v___x_166_, 4, v_toOne_162_);
v___x_167_ = lp_mathlib_Matrix_SpecialLinearGroup_toGL___redArg___lam__0(v___x_165_, v___x_163_, v___x_159_, v___x_166_);
v___x_168_ = lp_mathlib_Pi_mulSingle___redArg(v___f_164_, v_inst_155_, v_x_156_, v___x_167_, v_j_157_);
lean_dec_ref(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_tvAt(lean_object* v_00_u03b9_169_, lean_object* v_p_170_, lean_object* v_r_171_, lean_object* v_inst_172_, lean_object* v_hr_173_, lean_object* v_x_174_, lean_object* v_j_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lp_tree_Formalism_L2_NX_tvAt___redArg(v_p_170_, v_r_171_, v_inst_172_, v_x_174_, v_j_175_);
return v___x_176_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_NX_charOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lp_mathlib_Int_instAddMonoid;
v___x_178_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf___redArg(lean_object* v_inst_179_, lean_object* v_q_180_, lean_object* v_00_u03b6_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_toAddMonoidWithOne_185_; lean_object* v_toAddMonoid_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_toSemiring_190_; lean_object* v_toMonoid_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_toFun_195_; lean_object* v___x_196_; lean_object* v_toFun_197_; lean_object* v___x_198_; lean_object* v_toFun_199_; lean_object* v___x_200_; lean_object* v_toFun_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_182_ = lean_obj_once(&lp_tree_Formalism_L2_NX_charOf___redArg___closed__0, &lp_tree_Formalism_L2_NX_charOf___redArg___closed__0_once, _init_lp_tree_Formalism_L2_NX_charOf___redArg___closed__0);
lean_inc(v_q_180_);
v___x_183_ = lp_mathlib_ZMod_commRing(v_q_180_);
v___x_184_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_183_);
v_toAddMonoidWithOne_185_ = lean_ctor_get(v___x_184_, 1);
lean_inc_ref(v_toAddMonoidWithOne_185_);
lean_dec_ref(v___x_184_);
v_toAddMonoid_186_ = lean_ctor_get(v_toAddMonoidWithOne_185_, 1);
lean_inc_ref(v_toAddMonoid_186_);
lean_dec_ref(v_toAddMonoidWithOne_185_);
v___x_187_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_186_);
lean_dec_ref(v_toAddMonoid_186_);
v___x_188_ = lp_mathlib_Field_toSemifield___redArg(v_inst_179_);
v___x_189_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_188_);
v_toSemiring_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc_ref(v_toSemiring_190_);
lean_dec_ref(v___x_189_);
v_toMonoid_191_ = lean_ctor_get(v_toSemiring_190_, 1);
lean_inc_ref(v_toMonoid_191_);
lean_dec_ref(v_toSemiring_190_);
v___x_192_ = lp_mathlib_Units_instMulOneClass___redArg(v_toMonoid_191_);
v___x_193_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_191_);
v___x_194_ = lp_mathlib_zpowersHom___redArg(v___x_193_);
v_toFun_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_toFun_195_);
lean_dec_ref(v___x_194_);
v___x_196_ = lp_mathlib_MonoidHom_toAdditiveRight___redArg(v___x_182_, v___x_192_);
v_toFun_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_toFun_197_);
lean_dec_ref(v___x_196_);
v___x_198_ = lp_mathlib_ZMod_lift___redArg(v_q_180_);
v_toFun_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_toFun_199_);
lean_dec_ref(v___x_198_);
v___x_200_ = lp_mathlib_AddMonoidHom_toMultiplicativeLeft(lean_box(0), lean_box(0), v___x_187_, v___x_192_);
lean_dec_ref(v___x_192_);
lean_dec_ref(v___x_187_);
v_toFun_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_toFun_201_);
lean_dec_ref(v___x_200_);
v___x_202_ = lean_apply_1(v_toFun_195_, v_00_u03b6_181_);
v___x_203_ = lean_apply_1(v_toFun_197_, v___x_202_);
v___x_204_ = lean_apply_1(v_toFun_199_, v___x_203_);
v___x_205_ = lean_apply_1(v_toFun_201_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf___redArg___boxed(lean_object* v_inst_206_, lean_object* v_q_207_, lean_object* v_00_u03b6_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = lp_tree_Formalism_L2_NX_charOf___redArg(v_inst_206_, v_q_207_, v_00_u03b6_208_);
lean_dec_ref(v_inst_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf(lean_object* v_K_210_, lean_object* v_inst_211_, lean_object* v_q_212_, lean_object* v_00_u03b6_213_, lean_object* v_h_u03b6_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lp_tree_Formalism_L2_NX_charOf___redArg(v_inst_211_, v_q_212_, v_00_u03b6_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_charOf___boxed(lean_object* v_K_216_, lean_object* v_inst_217_, lean_object* v_q_218_, lean_object* v_00_u03b6_219_, lean_object* v_h_u03b6_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_tree_Formalism_L2_NX_charOf(v_K_216_, v_inst_217_, v_q_218_, v_00_u03b6_219_, v_h_u03b6_220_);
lean_dec_ref(v_inst_217_);
return v_res_221_;
}
}
static lean_object* _init_lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__5));
v___x_279_ = l_String_toRawSubstring_x27(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__14));
v___x_296_ = l_String_toRawSubstring_x27(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1(lean_object* v_x_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__17));
v___x_342_ = l_Lean_Syntax_isOfKind(v_x_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box(1);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_a_340_);
return v___x_344_;
}
else
{
lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; lean_object* v_ref_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_quotContext_345_ = lean_ctor_get(v_a_339_, 1);
v_currMacroScope_346_ = lean_ctor_get(v_a_339_, 2);
v_ref_347_ = lean_ctor_get(v_a_339_, 5);
v___x_348_ = 0;
v___x_349_ = l_Lean_SourceInfo_fromRef(v_ref_347_, v___x_348_);
v___x_350_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4));
v___x_351_ = lean_obj_once(&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6, &lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6_once, _init_lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6);
v___x_352_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9));
lean_inc_n(v_currMacroScope_346_, 2);
lean_inc_n(v_quotContext_345_, 2);
v___x_353_ = l_Lean_addMacroScope(v_quotContext_345_, v___x_352_, v_currMacroScope_346_);
v___x_354_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__11));
lean_inc_n(v___x_349_, 3);
v___x_355_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_355_, 0, v___x_349_);
lean_ctor_set(v___x_355_, 1, v___x_351_);
lean_ctor_set(v___x_355_, 2, v___x_353_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
v___x_356_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__13));
v___x_357_ = lean_obj_once(&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15, &lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15_once, _init_lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15);
v___x_358_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__16));
v___x_359_ = l_Lean_addMacroScope(v_quotContext_345_, v___x_358_, v_currMacroScope_346_);
v___x_360_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__31));
v___x_361_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_361_, 0, v___x_349_);
lean_ctor_set(v___x_361_, 1, v___x_357_);
lean_ctor_set(v___x_361_, 2, v___x_359_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
v___x_362_ = l_Lean_Syntax_node1(v___x_349_, v___x_356_, v___x_361_);
v___x_363_ = l_Lean_Syntax_node2(v___x_349_, v___x_350_, v___x_355_, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_a_340_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___boxed(lean_object* v_x_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1(v_x_365_, v_a_366_, v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_368_;
}
}
LEAN_EXPORT uint8_t lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__0(lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9));
v___x_371_ = l_Lean_Expr_isConstOf(v_x_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__0___boxed(lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__0(v_x_372_);
lean_dec_ref(v_x_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__1(lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___y_375_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__1___boxed(lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__1(v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__2(lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_ref_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_ref_400_ = lean_ctor_get(v___y_397_, 5);
v___x_401_ = 0;
v___x_402_ = l_Lean_SourceInfo_fromRef(v_ref_400_, v___x_401_);
v___x_403_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__17));
v___x_404_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__18));
lean_inc(v___x_402_);
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_Syntax_node1(v___x_402_, v___x_403_, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__2___boxed(lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__2(v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3(lean_object* v___f_422_, lean_object* v___f_423_, lean_object* v___f_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_432_ = lp_mathlib_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Topology___aux__Mathlib__Topology__Baire__BaireMeasurable______delab__app__Topology__term_u2200_u1d47___x2c____1_spec__0___redArg(v___y_425_);
lean_dec_ref(v___x_432_);
v___x_433_ = lean_alloc_closure((void*)(lp_mathlib_Mathlib_Notation3_matchExpr___boxed), 9, 1);
lean_closure_set(v___x_433_, 0, v___f_422_);
v___x_434_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___closed__2));
v___x_435_ = lean_alloc_closure((void*)(lp_mathlib_Mathlib_Notation3_matchApp___boxed), 10, 2);
lean_closure_set(v___x_435_, 0, v___x_433_);
lean_closure_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lp_mathlib_Mathlib_Notation3_MatchState_empty;
v___x_437_ = lp_mathlib_Mathlib_Notation3_matchApp(v___x_435_, v___f_423_, v___x_436_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; 
lean_dec_ref_known(v___x_437_, 1);
v___x_438_ = lp_mathlib_Mathlib_Notation3_withHeadRefIfTagAppFns(v___f_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_438_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v___f_424_);
v_a_439_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3___boxed(lean_object* v___f_447_, lean_object* v___f_448_, lean_object* v___f_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___lam__3(v___f_447_, v___f_448_, v___f_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1(lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4));
v___x_481_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__7));
v___x_482_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v___x_480_, v___x_481_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___boxed(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1(v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_TypeSpF(lean_object* v_L_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_n_495_, lean_object* v_K_496_, lean_object* v_inst_497_, lean_object* v_W_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_00_u03c1_501_, lean_object* v_J_502_, lean_object* v_00_u03c7_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_TypeSpF___boxed(lean_object* v_L_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_n_509_, lean_object* v_K_510_, lean_object* v_inst_511_, lean_object* v_W_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_00_u03c1_515_, lean_object* v_J_516_, lean_object* v_00_u03c7_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = lp_tree_Formalism_L2_NX_TypeSpF(v_L_505_, v_inst_506_, v_inst_507_, v_inst_508_, v_n_509_, v_K_510_, v_inst_511_, v_W_512_, v_inst_513_, v_inst_514_, v_00_u03c1_515_, v_J_516_, v_00_u03c7_517_);
lean_dec_ref(v_00_u03c7_517_);
lean_dec(v_00_u03c1_515_);
lean_dec(v_inst_514_);
lean_dec_ref(v_inst_513_);
lean_dec_ref(v_inst_511_);
lean_dec(v_n_509_);
lean_dec_ref(v_inst_506_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1(lean_object* v_x_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__1));
v___x_550_ = l_Lean_Syntax_isOfKind(v_x_546_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box(1);
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_a_548_);
return v___x_552_;
}
else
{
lean_object* v_quotContext_553_; lean_object* v_currMacroScope_554_; lean_object* v_ref_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_quotContext_553_ = lean_ctor_get(v_a_547_, 1);
v_currMacroScope_554_ = lean_ctor_get(v_a_547_, 2);
v_ref_555_ = lean_ctor_get(v_a_547_, 5);
v___x_556_ = 0;
v___x_557_ = l_Lean_SourceInfo_fromRef(v_ref_555_, v___x_556_);
v___x_558_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4));
v___x_559_ = lean_obj_once(&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6, &lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6_once, _init_lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__6);
v___x_560_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__9));
lean_inc_n(v_currMacroScope_554_, 2);
lean_inc_n(v_quotContext_553_, 2);
v___x_561_ = l_Lean_addMacroScope(v_quotContext_553_, v___x_560_, v_currMacroScope_554_);
v___x_562_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__11));
lean_inc_n(v___x_557_, 3);
v___x_563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_563_, 0, v___x_557_);
lean_ctor_set(v___x_563_, 1, v___x_559_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
v___x_564_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__13));
v___x_565_ = lean_obj_once(&lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15, &lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15_once, _init_lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__15);
v___x_566_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__16));
v___x_567_ = l_Lean_addMacroScope(v_quotContext_553_, v___x_566_, v_currMacroScope_554_);
v___x_568_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__5));
v___x_569_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_569_, 0, v___x_557_);
lean_ctor_set(v___x_569_, 1, v___x_565_);
lean_ctor_set(v___x_569_, 2, v___x_567_);
lean_ctor_set(v___x_569_, 3, v___x_568_);
v___x_570_ = l_Lean_Syntax_node1(v___x_557_, v___x_564_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node2(v___x_557_, v___x_558_, v___x_563_, v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_548_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___boxed(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______macroRules____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1(v_x_573_, v_a_574_, v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___lam__2(lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_ref_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_ref_584_ = lean_ctor_get(v___y_581_, 5);
v___x_585_ = 0;
v___x_586_ = l_Lean_SourceInfo_fromRef(v_ref_584_, v___x_585_);
v___x_587_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a__1___closed__1));
v___x_588_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX_termL_u207a___closed__18));
lean_inc(v___x_586_);
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_586_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_Syntax_node1(v___x_586_, v___x_587_, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___lam__2___boxed(lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___lam__2(v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1(lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1___closed__4));
v___x_619_ = ((lean_object*)(lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___closed__3));
v___x_620_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v___x_618_, v___x_619_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1___boxed(lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = lp_tree___private_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs_0__Formalism_L2_NX___aux__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs______delab__app____private__Formalism__LocalToGlobal__NormalizedHeckeFactors__ExpDefs__0__Formalism__L2__NX__termL_u207a__1__1(v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_628_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_NX_detT___redArg___lam__0(lean_object* v_r_629_, lean_object* v_a_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_le(v_r_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg___lam__0___boxed(lean_object* v_r_632_, lean_object* v_a_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = lp_tree_Formalism_L2_NX_detT___redArg___lam__0(v_r_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec(v_r_632_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg___lam__1(lean_object* v_a_636_){
_start:
{
lean_inc(v_a_636_);
return v_a_636_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg___lam__1___boxed(lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = lp_tree_Formalism_L2_NX_detT___redArg___lam__1(v_a_637_);
lean_dec(v_a_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT___redArg(lean_object* v_n_641_, lean_object* v_r_642_, lean_object* v_inst_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___f_645_; lean_object* v___f_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_18__overap_651_; lean_object* v___x_652_; 
v___f_645_ = ((lean_object*)(lp_tree_Formalism_L2_NX_detT___redArg___closed__0));
v___f_646_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NX_detT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_646_, 0, v_r_642_);
v___f_647_ = ((lean_object*)(lp_tree_Formalism_L2_NX_detT___redArg___closed__1));
v___x_648_ = l_List_finRange(v_n_641_);
v___x_649_ = lp_mathlib_Subtype_fintype___redArg(v___f_646_, v___x_648_);
v___x_650_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, lean_box(0));
lean_closure_set(v___x_650_, 2, lean_box(0));
lean_closure_set(v___x_650_, 3, lean_box(0));
lean_closure_set(v___x_650_, 4, lean_box(0));
lean_closure_set(v___x_650_, 5, v_x_644_);
lean_closure_set(v___x_650_, 6, v___f_647_);
lean_closure_set(v___x_650_, 7, v___f_647_);
v___x_18__overap_651_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___f_645_, v___x_649_, v_inst_643_);
v___x_652_ = lean_apply_1(v___x_18__overap_651_, v___x_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_detT(lean_object* v_n_653_, lean_object* v_r_654_, lean_object* v_R_655_, lean_object* v_inst_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lp_tree_Formalism_L2_NX_detT___redArg(v_n_653_, v_r_654_, v_inst_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___redArg___lam__0(lean_object* v___y_659_){
_start:
{
lean_inc(v___y_659_);
return v___y_659_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___redArg___lam__0___boxed(lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = lp_tree_Formalism_L2_NX_topR___redArg___lam__0(v___y_660_);
lean_dec(v___y_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___redArg(lean_object* v_x_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_667_; 
v___f_666_ = ((lean_object*)(lp_tree_Formalism_L2_NX_topR___redArg___closed__0));
v___x_667_ = lp_mathlib_Matrix_submatrix___redArg(v_x_663_, v___f_666_, v___f_666_, v_a_664_, v_a_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR(lean_object* v_n_668_, lean_object* v_r_669_, lean_object* v_h_670_, lean_object* v_R_671_, lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = lp_tree_Formalism_L2_NX_topR___redArg(v_x_672_, v_a_673_, v_a_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NX_topR___boxed(lean_object* v_n_676_, lean_object* v_r_677_, lean_object* v_h_678_, lean_object* v_R_679_, lean_object* v_x_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = lp_tree_Formalism_L2_NX_topR(v_n_676_, v_r_677_, v_h_678_, v_R_679_, v_x_680_, v_a_681_, v_a_682_);
lean_dec(v_r_677_);
lean_dec(v_n_676_);
return v_res_683_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_AlgebraicWeights_IsAlgWeight(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_AlgebraicWeights_IsAlgWeight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
