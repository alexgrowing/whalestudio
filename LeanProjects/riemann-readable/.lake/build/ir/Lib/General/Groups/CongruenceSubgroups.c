// Lean compiler output
// Module: Lib.General.Groups.CongruenceSubgroups
// Imports: public import Init public meta import Init public import Lib.Base
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
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MeasurableSpace_pi___redArg();
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_map___redArg(lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instIntCast___lam__0(lean_object*);
extern lean_object* lp_mathlib_Complex_instZero;
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_transvection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_MulEquiv_piUnits___redArg();
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonalRingHom___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_SubgroupClass_toGroup___redArg(lean_object*);
lean_object* lp_mathlib_MonoidHom_toHomUnits___redArg(lean_object*, lean_object*);
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__0 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__1 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__2 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__3 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__4 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__4_value;
static const lean_array_object lp_GRH_IsCompact_preimage__val___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__5 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__5_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__6 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__7 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__7_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__8 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__9 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__9_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticInfer_instance"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__10 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(131, 220, 172, 177, 143, 161, 43, 73)}};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__11 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__11_value;
static const lean_string_object lp_GRH_IsCompact_preimage__val___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "infer_instance"};
static const lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__12 = (const lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__12_value;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__13;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__14;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__15;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__16;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__17;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__18;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__19;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__20;
static lean_once_cell_t lp_GRH_IsCompact_preimage__val___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_preimage__val___auto__1___closed__21;
LEAN_EXPORT lean_object* lp_GRH_IsCompact_preimage__val___auto__1;
static const lean_string_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Mathlib"};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__0 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__0_value;
static const lean_string_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__1 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__1_value;
static const lean_string_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunProp"};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__2 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__2_value;
static const lean_string_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funPropTacStx"};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__3 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 213, 161, 2, 73, 184, 31, 228)}};
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 10, 180, 159, 248, 97, 218, 144)}};
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 118, 4, 116, 28, 199, 219)}};
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(146, 162, 46, 139, 110, 137, 217, 136)}};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4_value;
static const lean_string_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fun_prop"};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__5 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__5_value;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__6;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__7;
static const lean_string_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__8 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value_aux_0),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value_aux_1),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value_aux_2),((lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9_value;
static const lean_ctor_object lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__9_value),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10 = (const lean_object*)&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10_value;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__11;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__14;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__15;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__16;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__17;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__18;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__19;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__20;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__21;
static lean_once_cell_t lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22;
LEAN_EXPORT lean_object* lp_GRH_IsCompact_image__of__continuous___auto__1;
LEAN_EXPORT lean_object* lp_GRH_IsOpen_preimage__of__continuous___auto__1;
LEAN_EXPORT lean_object* lp_GRH_IsClosed_preimage__of__continuous___auto__1;
LEAN_EXPORT lean_object* lp_GRH_IsCompact_integrableOn___auto__1;
LEAN_EXPORT lean_object* lp_GRH_HasCompactSupport_integrable___auto__1;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discharger"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__0_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value_aux_0),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value_aux_1),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value_aux_2),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 186, 255, 143, 150, 72, 152, 71)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__2_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__3;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__4;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__5_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__6_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "disch"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__9_value_aux_0),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(127, 235, 222, 140, 231, 248, 247, 8)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__9_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__10;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__11;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__13;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__14;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__15;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__16_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__17;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__18;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__19 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__19_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value_aux_0),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value_aux_1),((lean_object*)&lp_GRH_IsCompact_preimage__val___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value_aux_2),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__26;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__27;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__28;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__32;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__33;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__35;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__36 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__36_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__37;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__38;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__39;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__40;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__41;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__42;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__43;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__44;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__45;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__46;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__47;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__48;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__49;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__50;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1;
static lean_once_cell_t lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_inclMatrix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_inclMatrix___redArg___closed__0 = (const lean_object*)&lp_GRH_New_inclMatrix___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_signMatrix___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_signMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_signMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_diagGL___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_diagGL___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_diagGL___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_diagGL___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_diagGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_diagGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_diagGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_transposeGL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_transposeGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_transposeGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_transvectionGL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_transvectionGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_transvectionGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_intGL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_intGL_toMatrix___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_intGL_toMatrix___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intGL_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_U___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_USign___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_USign___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_USign(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_USign___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___closed__0 = (const lean_object*)&lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_map___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_U_map___auto__3;
static const lean_closure_object lp_GRH_New_U_map___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_U_map___redArg___closed__0 = (const lean_object*)&lp_GRH_New_U_map___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_U_map___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_det___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_det___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_det(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_det___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_continuous__map___auto__1;
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__13(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__12));
v___x_29_ = l_Lean_mkAtom(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__14(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__13, &lp_GRH_IsCompact_preimage__val___auto__1___closed__13_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__13);
v___x_31_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_32_ = lean_array_push(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_33_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__14, &lp_GRH_IsCompact_preimage__val___auto__1___closed__14_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__14);
v___x_34_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__11));
v___x_35_ = lean_box(2);
v___x_36_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
lean_ctor_set(v___x_36_, 2, v___x_33_);
return v___x_36_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__16(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__15, &lp_GRH_IsCompact_preimage__val___auto__1___closed__15_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__15);
v___x_38_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_39_ = lean_array_push(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__17(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__16, &lp_GRH_IsCompact_preimage__val___auto__1___closed__16_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__16);
v___x_41_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__9));
v___x_42_ = lean_box(2);
v___x_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___x_40_);
return v___x_43_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__17, &lp_GRH_IsCompact_preimage__val___auto__1___closed__17_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__17);
v___x_45_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__18, &lp_GRH_IsCompact_preimage__val___auto__1___closed__18_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__18);
v___x_48_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__7));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__19, &lp_GRH_IsCompact_preimage__val___auto__1___closed__19_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__19);
v___x_52_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__20, &lp_GRH_IsCompact_preimage__val___auto__1___closed__20_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__20);
v___x_55_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__4));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_lp_GRH_IsCompact_preimage__val___auto__1(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&lp_GRH_IsCompact_preimage__val___auto__1___closed__21, &lp_GRH_IsCompact_preimage__val___auto__1___closed__21_once, _init_lp_GRH_IsCompact_preimage__val___auto__1___closed__21);
return v___x_58_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__6(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__5));
v___x_70_ = l_Lean_mkAtom(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__7(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__6, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__6_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__6);
v___x_72_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_73_ = lean_array_push(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__11(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_85_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_86_ = lean_array_push(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__11, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__11_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__11);
v___x_88_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__9));
v___x_89_ = lean_box(2);
v___x_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12);
v___x_92_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__7, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__7_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__7);
v___x_93_ = lean_array_push(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__14(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_95_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13);
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__15(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_98_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__14, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__14_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__14);
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__16(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__15, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__15_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__15);
v___x_101_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4));
v___x_102_ = lean_box(2);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__17(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__16, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__16_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__16);
v___x_105_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_106_ = lean_array_push(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__18(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__17, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__17_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__17);
v___x_108_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__9));
v___x_109_ = lean_box(2);
v___x_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_107_);
return v___x_110_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__19(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__18, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__18_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__18);
v___x_112_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__20(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__19, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__19_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__19);
v___x_115_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__7));
v___x_116_ = lean_box(2);
v___x_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__21(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__20, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__20_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__20);
v___x_119_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_120_ = lean_array_push(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__21, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__21_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__21);
v___x_122_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__4));
v___x_123_ = lean_box(2);
v___x_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_lp_GRH_IsCompact_image__of__continuous___auto__1(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22);
return v___x_125_;
}
}
static lean_object* _init_lp_GRH_IsOpen_preimage__of__continuous___auto__1(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22);
return v___x_126_;
}
}
static lean_object* _init_lp_GRH_IsClosed_preimage__of__continuous___auto__1(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22);
return v___x_127_;
}
}
static lean_object* _init_lp_GRH_IsCompact_integrableOn___auto__1(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22);
return v___x_128_;
}
}
static lean_object* _init_lp_GRH_HasCompactSupport_integrable___auto__1(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22);
return v___x_129_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__3(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__2));
v___x_138_ = l_Lean_mkAtom(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__4(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__3, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__3_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__3);
v___x_140_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_141_ = lean_array_push(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__10(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__8));
v___x_151_ = l_Lean_mkAtom(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__11(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__10, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__10_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__10);
v___x_153_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_154_ = lean_array_push(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__12(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__11, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__11_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__11);
v___x_156_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__9));
v___x_157_ = lean_box(2);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_155_);
return v___x_158_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__13(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__12, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__12_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__12);
v___x_160_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_161_ = lean_array_push(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__14(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__13, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__13_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__13);
v___x_163_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__6));
v___x_164_ = lean_box(2);
v___x_165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__15(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__14, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__14_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__14);
v___x_167_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__4, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__4_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__4);
v___x_168_ = lean_array_push(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__17(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__16));
v___x_171_ = l_Lean_mkAtom(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__18(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__17, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__17_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__17);
v___x_173_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__15, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__15_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__15);
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__21(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__19));
v___x_182_ = l_Lean_mkAtom(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__22(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__21, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__21_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__21);
v___x_184_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_185_ = lean_array_push(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__23(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__12);
v___x_187_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__22, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__22_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__22);
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__24(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_190_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__23, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__23_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__23);
v___x_191_ = lean_array_push(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__25(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_193_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__24, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__24_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__24);
v___x_194_ = lean_array_push(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__26(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_196_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__25, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__25_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__25);
v___x_197_ = lean_array_push(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__27(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_199_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__26, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__26_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__26);
v___x_200_ = lean_array_push(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__28(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__27, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__27_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__27);
v___x_202_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__20));
v___x_203_ = lean_box(2);
v___x_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_201_);
return v___x_204_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__29(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__28, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__28_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__28);
v___x_206_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_207_ = lean_array_push(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__30(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__29, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__29_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__29);
v___x_209_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__9));
v___x_210_ = lean_box(2);
v___x_211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
lean_ctor_set(v___x_211_, 2, v___x_208_);
return v___x_211_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__31(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__30, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__30_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__30);
v___x_213_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_214_ = lean_array_push(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__32(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__31, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__31_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__31);
v___x_216_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__7));
v___x_217_ = lean_box(2);
v___x_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
lean_ctor_set(v___x_218_, 2, v___x_215_);
return v___x_218_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__33(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__32, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__32_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__32);
v___x_220_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_221_ = lean_array_push(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__33, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__33_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__33);
v___x_223_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__4));
v___x_224_ = lean_box(2);
v___x_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_222_);
return v___x_225_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__35(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34);
v___x_227_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__18, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__18_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__18);
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__37(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__36));
v___x_231_ = l_Lean_mkAtom(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__38(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__37, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__37_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__37);
v___x_233_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__35, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__35_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__35);
v___x_234_ = lean_array_push(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__39(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__38, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__38_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__38);
v___x_236_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__1));
v___x_237_ = lean_box(2);
v___x_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_235_);
return v___x_238_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__40(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__39, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__39_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__39);
v___x_240_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_241_ = lean_array_push(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__41(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__40, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__40_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__40);
v___x_243_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__9));
v___x_244_ = lean_box(2);
v___x_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
return v___x_245_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__42(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__41, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__41_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__41);
v___x_247_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__13);
v___x_248_ = lean_array_push(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__43(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__10));
v___x_250_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__42, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__42_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__42);
v___x_251_ = lean_array_push(v___x_250_, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__44(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__43, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__43_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__43);
v___x_253_ = ((lean_object*)(lp_GRH_IsCompact_image__of__continuous___auto__1___closed__4));
v___x_254_ = lean_box(2);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
return v___x_255_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__45(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__44, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__44_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__44);
v___x_257_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_258_ = lean_array_push(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__46(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__45, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__45_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__45);
v___x_260_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__9));
v___x_261_ = lean_box(2);
v___x_262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
lean_ctor_set(v___x_262_, 2, v___x_259_);
return v___x_262_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__47(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__46, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__46_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__46);
v___x_264_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_265_ = lean_array_push(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__48(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_266_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__47, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__47_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__47);
v___x_267_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__7));
v___x_268_ = lean_box(2);
v___x_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_266_);
return v___x_269_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__49(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__48, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__48_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__48);
v___x_271_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__5));
v___x_272_ = lean_array_push(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__50(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__49, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__49_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__49);
v___x_274_ = ((lean_object*)(lp_GRH_IsCompact_preimage__val___auto__1___closed__4));
v___x_275_ = lean_box(2);
v___x_276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
return v___x_276_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__50, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__50_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__50);
return v___x_277_;
}
}
static lean_object* _init_lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lp_mathlib_MeasurableSpace_pi___redArg();
return v___x_278_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg(){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0, &lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0_once, _init_lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___boxed(lean_object* v___dummy_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg();
return v_res_282_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instMeasurableSpaceMatrix__lib(lean_object* v_m_283_, lean_object* v_n_284_, lean_object* v_R_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0, &lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0_once, _init_lp_GRH_New_instMeasurableSpaceMatrix__lib___redArg___closed__0);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___redArg___lam__0(lean_object* v_inst_288_, lean_object* v_x_289_){
_start:
{
lean_inc(v_inst_288_);
return v_inst_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___redArg___lam__0___boxed(lean_object* v_inst_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_GRH_New_inclMatrix___redArg___lam__0(v_inst_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec(v_inst_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___redArg(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_u_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___f_300_ = lean_alloc_closure((void*)(lp_GRH_New_inclMatrix___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_300_, 0, v_inst_296_);
v___x_301_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_301_, 0, lean_box(0));
lean_closure_set(v___x_301_, 1, lean_box(0));
lean_closure_set(v___x_301_, 2, v_inst_294_);
lean_closure_set(v___x_301_, 3, v_inst_295_);
lean_closure_set(v___x_301_, 4, v___f_300_);
v___x_302_ = ((lean_object*)(lp_GRH_New_inclMatrix___redArg___closed__0));
v___x_303_ = lp_mathlib_Matrix_submatrix___redArg(v___x_301_, v___x_302_, v_u_297_, v_a_298_, v_a_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix(lean_object* v_m_304_, lean_object* v_n_305_, lean_object* v_inst_306_, lean_object* v_R_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_u_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lp_GRH_New_inclMatrix___redArg(v_inst_306_, v_inst_308_, v_inst_309_, v_u_310_, v_a_311_, v_a_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_signMatrix___redArg___lam__0(lean_object* v_s_314_, lean_object* v_i_315_){
_start:
{
lean_object* v___x_316_; lean_object* v_val_317_; lean_object* v___x_318_; 
v___x_316_ = lean_apply_1(v_s_314_, v_i_315_);
v_val_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___x_316_);
v___x_318_ = lp_mathlib_Complex_instIntCast___lam__0(v_val_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_signMatrix___redArg(lean_object* v_inst_319_, lean_object* v_s_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___f_323_ = lean_alloc_closure((void*)(lp_GRH_New_signMatrix___redArg___lam__0), 2, 1);
lean_closure_set(v___f_323_, 0, v_s_320_);
v___x_324_ = lp_mathlib_Complex_instZero;
v___x_325_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_319_, v___x_324_, v___f_323_, v_a_321_, v_a_322_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_signMatrix(lean_object* v_n_326_, lean_object* v_inst_327_, lean_object* v_s_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lp_GRH_New_signMatrix___redArg(v_inst_327_, v_s_328_, v_a_329_, v_a_330_);
return v___x_331_;
}
}
static lean_object* _init_lp_GRH_New_diagGL___redArg___closed__0(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lp_mathlib_MulEquiv_piUnits___redArg();
return v___x_332_;
}
}
static lean_object* _init_lp_GRH_New_diagGL___redArg___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&lp_GRH_New_diagGL___redArg___closed__0, &lp_GRH_New_diagGL___redArg___closed__0_once, _init_lp_GRH_New_diagGL___redArg___closed__0);
v___x_334_ = lp_mathlib_Equiv_symm___redArg(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_diagGL___redArg(lean_object* v_inst_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v_toSemiring_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_toFun_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___f_343_; 
v_toSemiring_337_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toSemiring_337_);
lean_dec_ref(v_inst_336_);
v___x_338_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_337_);
v___x_339_ = lean_obj_once(&lp_GRH_New_diagGL___redArg___closed__1, &lp_GRH_New_diagGL___redArg___closed__1_once, _init_lp_GRH_New_diagGL___redArg___closed__1);
v_toFun_340_ = lean_ctor_get(v___x_339_, 0);
v___x_341_ = lp_mathlib_Matrix_diagonalRingHom___redArg(v___x_338_, v_inst_335_);
v___f_342_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_342_, 0, v___x_341_);
lean_inc(v_toFun_340_);
v___f_343_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_343_, 0, v_toFun_340_);
lean_closure_set(v___f_343_, 1, v___f_342_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_diagGL(lean_object* v_n_344_, lean_object* v_R_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lp_GRH_New_diagGL___redArg(v_inst_346_, v_inst_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_diagGL___boxed(lean_object* v_n_350_, lean_object* v_R_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = lp_GRH_New_diagGL(v_n_350_, v_R_351_, v_inst_352_, v_inst_353_, v_inst_354_);
lean_dec(v_inst_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_transposeGL___redArg(lean_object* v_g_356_){
_start:
{
lean_object* v_val_357_; lean_object* v_inv_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_367_; 
v_val_357_ = lean_ctor_get(v_g_356_, 0);
v_inv_358_ = lean_ctor_get(v_g_356_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_g_356_);
if (v_isSharedCheck_367_ == 0)
{
v___x_360_ = v_g_356_;
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_inv_358_);
lean_inc(v_val_357_);
lean_dec(v_g_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_362_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_362_, 0, lean_box(0));
lean_closure_set(v___x_362_, 1, lean_box(0));
lean_closure_set(v___x_362_, 2, lean_box(0));
lean_closure_set(v___x_362_, 3, v_val_357_);
v___x_363_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_363_, 0, lean_box(0));
lean_closure_set(v___x_363_, 1, lean_box(0));
lean_closure_set(v___x_363_, 2, lean_box(0));
lean_closure_set(v___x_363_, 3, v_inv_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_363_);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_transposeGL(lean_object* v_n_368_, lean_object* v_R_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_g_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lp_GRH_New_transposeGL___redArg(v_g_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_transposeGL___boxed(lean_object* v_n_375_, lean_object* v_R_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_g_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = lp_GRH_New_transposeGL(v_n_375_, v_R_376_, v_inst_377_, v_inst_378_, v_inst_379_, v_g_380_);
lean_dec_ref(v_inst_379_);
lean_dec(v_inst_378_);
lean_dec_ref(v_inst_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_transvectionGL___redArg(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_i_384_, lean_object* v_j_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_toNeg_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v___x_387_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_383_);
v___x_388_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_387_);
lean_dec_ref(v___x_387_);
v_toNeg_389_ = lean_ctor_get(v___x_388_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_388_, 0);
lean_dec(v_unused_400_);
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_toNeg_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
lean_inc(v_a_386_);
lean_inc(v_j_385_);
lean_inc(v_i_384_);
lean_inc_ref(v_inst_383_);
lean_inc_ref(v_inst_382_);
v___x_393_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transvection), 9, 7);
lean_closure_set(v___x_393_, 0, lean_box(0));
lean_closure_set(v___x_393_, 1, lean_box(0));
lean_closure_set(v___x_393_, 2, v_inst_382_);
lean_closure_set(v___x_393_, 3, v_inst_383_);
lean_closure_set(v___x_393_, 4, v_i_384_);
lean_closure_set(v___x_393_, 5, v_j_385_);
lean_closure_set(v___x_393_, 6, v_a_386_);
v___x_394_ = lean_apply_1(v_toNeg_389_, v_a_386_);
v___x_395_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transvection), 9, 7);
lean_closure_set(v___x_395_, 0, lean_box(0));
lean_closure_set(v___x_395_, 1, lean_box(0));
lean_closure_set(v___x_395_, 2, v_inst_382_);
lean_closure_set(v___x_395_, 3, v_inst_383_);
lean_closure_set(v___x_395_, 4, v_i_384_);
lean_closure_set(v___x_395_, 5, v_j_385_);
lean_closure_set(v___x_395_, 6, v___x_394_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_395_);
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_397_ = v___x_391_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_transvectionGL(lean_object* v_n_401_, lean_object* v_R_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_i_406_, lean_object* v_j_407_, lean_object* v_h_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lp_GRH_New_transvectionGL___redArg(v_inst_403_, v_inst_405_, v_i_406_, v_j_407_, v_a_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_transvectionGL___boxed(lean_object* v_n_411_, lean_object* v_R_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_i_416_, lean_object* v_j_417_, lean_object* v_h_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = lp_GRH_New_transvectionGL(v_n_411_, v_R_412_, v_inst_413_, v_inst_414_, v_inst_415_, v_i_416_, v_j_417_, v_h_418_, v_a_419_);
lean_dec(v_inst_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL___redArg(){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL___redArg___boxed(lean_object* v___dummy_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = lp_GRH_New_intGL___redArg();
return v_res_424_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL(lean_object* v_R_425_, lean_object* v_inst_426_, lean_object* v_n_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_O_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL___boxed(lean_object* v_R_432_, lean_object* v_inst_433_, lean_object* v_n_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_O_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = lp_GRH_New_intGL(v_R_432_, v_inst_433_, v_n_434_, v_inst_435_, v_inst_436_, v_O_437_);
lean_dec_ref(v_inst_436_);
lean_dec(v_inst_435_);
lean_dec_ref(v_inst_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix___redArg___lam__0(lean_object* v_k_439_, lean_object* v_i_440_, lean_object* v_j_441_){
_start:
{
lean_object* v_val_442_; lean_object* v___x_443_; 
v_val_442_ = lean_ctor_get(v_k_439_, 0);
lean_inc(v_val_442_);
lean_dec_ref(v_k_439_);
v___x_443_ = lean_apply_2(v_val_442_, v_i_440_, v_j_441_);
return v___x_443_;
}
}
static lean_object* _init_lp_GRH_New_intGL_toMatrix___redArg___closed__0(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lp_mathlib_Equiv_refl___redArg();
return v___x_444_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix___redArg(lean_object* v_k_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; lean_object* v_toFun_449_; lean_object* v___f_450_; lean_object* v___x_451_; 
v___x_448_ = lean_obj_once(&lp_GRH_New_intGL_toMatrix___redArg___closed__0, &lp_GRH_New_intGL_toMatrix___redArg___closed__0_once, _init_lp_GRH_New_intGL_toMatrix___redArg___closed__0);
v_toFun_449_ = lean_ctor_get(v___x_448_, 0);
v___f_450_ = lean_alloc_closure((void*)(lp_GRH_New_intGL_toMatrix___redArg___lam__0), 3, 1);
lean_closure_set(v___f_450_, 0, v_k_445_);
lean_inc(v_toFun_449_);
v___x_451_ = lean_apply_3(v_toFun_449_, v___f_450_, v_a_446_, v_a_447_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix(lean_object* v_n_452_, lean_object* v_R_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_O_457_, lean_object* v_k_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lp_GRH_New_intGL_toMatrix___redArg(v_k_458_, v_a_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_toMatrix___boxed(lean_object* v_n_462_, lean_object* v_R_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_O_467_, lean_object* v_k_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = lp_GRH_New_intGL_toMatrix(v_n_462_, v_R_463_, v_inst_464_, v_inst_465_, v_inst_466_, v_O_467_, v_k_468_, v_a_469_, v_a_470_);
lean_dec_ref(v_inst_466_);
lean_dec(v_inst_465_);
lean_dec_ref(v_inst_464_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_map___redArg(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_O_475_, lean_object* v_f_476_){
_start:
{
lean_object* v_toSemiring_477_; lean_object* v___x_478_; lean_object* v_toMonoid_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___f_485_; 
v_toSemiring_477_ = lean_ctor_get(v_inst_474_, 0);
lean_inc_ref(v_inst_472_);
lean_inc(v_inst_473_);
lean_inc_ref(v_toSemiring_477_);
v___x_478_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_477_, v_inst_473_, v_inst_472_);
v_toMonoid_479_ = lean_ctor_get(v___x_478_, 1);
lean_inc_ref(v_toMonoid_479_);
lean_dec_ref(v___x_478_);
v___x_480_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_479_);
v___x_481_ = lp_mathlib_Matrix_GeneralLinearGroup_map___redArg(v_f_476_);
v___x_482_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_480_);
v___x_483_ = lean_alloc_closure((void*)(lp_GRH_New_intGL_toMatrix___boxed), 9, 6);
lean_closure_set(v___x_483_, 0, lean_box(0));
lean_closure_set(v___x_483_, 1, lean_box(0));
lean_closure_set(v___x_483_, 2, v_inst_472_);
lean_closure_set(v___x_483_, 3, v_inst_473_);
lean_closure_set(v___x_483_, 4, v_inst_474_);
lean_closure_set(v___x_483_, 5, v_O_475_);
v___x_484_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_482_, v___x_483_);
lean_dec_ref(v___x_482_);
v___f_485_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_485_, 0, v___x_484_);
lean_closure_set(v___f_485_, 1, v___x_481_);
return v___f_485_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_map(lean_object* v_n_486_, lean_object* v_R_487_, lean_object* v_S_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_O_493_, lean_object* v_f_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lp_GRH_New_intGL_map___redArg(v_inst_489_, v_inst_490_, v_inst_491_, v_O_493_, v_f_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intGL_map___boxed(lean_object* v_n_496_, lean_object* v_R_497_, lean_object* v_S_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_O_503_, lean_object* v_f_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = lp_GRH_New_intGL_map(v_n_496_, v_R_497_, v_S_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_inst_502_, v_O_503_, v_f_504_);
lean_dec_ref(v_inst_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL___redArg(){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL___redArg___boxed(lean_object* v___dummy_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = lp_GRH_New_congruenceGL___redArg();
return v_res_509_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL(lean_object* v_m_510_, lean_object* v_n_511_, lean_object* v_R_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_O_516_, lean_object* v_M_517_, lean_object* v_e_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_box(0);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceGL___boxed(lean_object* v_m_520_, lean_object* v_n_521_, lean_object* v_R_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_O_526_, lean_object* v_M_527_, lean_object* v_e_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = lp_GRH_New_congruenceGL(v_m_520_, v_n_521_, v_R_522_, v_inst_523_, v_inst_524_, v_inst_525_, v_O_526_, v_M_527_, v_e_528_);
lean_dec(v_e_528_);
lean_dec_ref(v_inst_525_);
lean_dec(v_inst_524_);
lean_dec_ref(v_inst_523_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U___redArg(){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U___redArg___boxed(lean_object* v___dummy_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = lp_GRH_New_U___redArg();
return v_res_533_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U(lean_object* v_n_534_, lean_object* v_R_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_J_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_box(0);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U___boxed(lean_object* v_n_542_, lean_object* v_R_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_J_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = lp_GRH_New_U(v_n_542_, v_R_543_, v_inst_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_J_548_);
lean_dec(v_J_548_);
lean_dec_ref(v_inst_547_);
lean_dec(v_inst_546_);
lean_dec_ref(v_inst_545_);
lean_dec(v_inst_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_USign___redArg(){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(0);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_USign___redArg___boxed(lean_object* v___dummy_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = lp_GRH_New_USign___redArg();
return v_res_553_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_USign(lean_object* v_n_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_00_u03b5_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_USign___boxed(lean_object* v_n_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_00_u03b5_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = lp_GRH_New_USign(v_n_559_, v_inst_560_, v_inst_561_, v_00_u03b5_562_);
lean_dec_ref(v_00_u03b5_562_);
lean_dec_ref(v_inst_561_);
lean_dec(v_inst_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___lam__0(lean_object* v_x_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_val_567_; lean_object* v___x_568_; 
v_val_567_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_val_567_);
lean_dec_ref(v_x_564_);
v___x_568_ = lean_apply_2(v_val_567_, v___y_565_, v___y_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg(){
_start:
{
lean_object* v___f_571_; 
v___f_571_ = ((lean_object*)(lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___closed__0));
return v___f_571_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___boxed(lean_object* v___dummy_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg();
return v_res_573_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix(lean_object* v_n_574_, lean_object* v_R_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_J_580_){
_start:
{
lean_object* v___f_581_; 
v___f_581_ = ((lean_object*)(lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___redArg___closed__0));
return v___f_581_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix___boxed(lean_object* v_n_582_, lean_object* v_R_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_J_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = lp_GRH_New_instCoeOutSubtypeGeneralLinearGroupMemSubgroupUMatrix(v_n_582_, v_R_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_J_588_);
lean_dec(v_J_588_);
lean_dec_ref(v_inst_587_);
lean_dec(v_inst_586_);
lean_dec_ref(v_inst_585_);
lean_dec(v_inst_584_);
return v_res_589_;
}
}
static lean_object* _init_lp_GRH_New_U_map___auto__1(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34);
return v___x_590_;
}
}
static lean_object* _init_lp_GRH_New_U_map___auto__3(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34, &lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34_once, _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1___closed__34);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_map___redArg(lean_object* v_f_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; 
v___x_594_ = lp_mathlib_Matrix_GeneralLinearGroup_map___redArg(v_f_593_);
v___f_595_ = ((lean_object*)(lp_GRH_New_U_map___redArg___closed__0));
v___f_596_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_596_, 0, v___f_595_);
lean_closure_set(v___f_596_, 1, v___x_594_);
v___f_597_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_597_, 0, v___f_596_);
return v___f_597_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_map(lean_object* v_n_598_, lean_object* v_R_599_, lean_object* v_S_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_f_607_, lean_object* v_hf_608_, lean_object* v_J_609_, lean_object* v_J_x27_610_, lean_object* v_h_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lp_GRH_New_U_map___redArg(v_f_607_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_map___boxed(lean_object* v_n_613_, lean_object* v_R_614_, lean_object* v_S_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_f_622_, lean_object* v_hf_623_, lean_object* v_J_624_, lean_object* v_J_x27_625_, lean_object* v_h_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = lp_GRH_New_U_map(v_n_613_, v_R_614_, v_S_615_, v_inst_616_, v_inst_617_, v_inst_618_, v_inst_619_, v_inst_620_, v_inst_621_, v_f_622_, v_hf_623_, v_J_624_, v_J_x27_625_, v_h_626_);
lean_dec(v_J_x27_625_);
lean_dec(v_J_624_);
lean_dec_ref(v_inst_621_);
lean_dec(v_inst_620_);
lean_dec(v_inst_619_);
lean_dec_ref(v_inst_618_);
lean_dec_ref(v_inst_617_);
lean_dec(v_inst_616_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__0(lean_object* v_inv_628_, lean_object* v___y_629_, lean_object* v_j_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_apply_2(v_inv_628_, v_j_630_, v___y_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__1(lean_object* v_val_632_, lean_object* v___y_633_, lean_object* v_j_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_apply_2(v_val_632_, v___y_633_, v_j_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__2(lean_object* v_val_636_, lean_object* v_j_637_, lean_object* v_j_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = lean_apply_2(v_val_636_, v_j_638_, v_j_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__3(lean_object* v_val_640_, lean_object* v_inst_641_, lean_object* v_toMul_642_, lean_object* v_toAddCommMonoid_643_, lean_object* v___f_644_, lean_object* v_j_645_){
_start:
{
lean_object* v___f_646_; lean_object* v___x_647_; 
v___f_646_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__2), 3, 2);
lean_closure_set(v___f_646_, 0, v_val_640_);
lean_closure_set(v___f_646_, 1, v_j_645_);
v___x_647_ = lp_mathlib_dotProduct___redArg(v_inst_641_, v_toMul_642_, v_toAddCommMonoid_643_, v___f_644_, v___f_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__3___boxed(lean_object* v_val_648_, lean_object* v_inst_649_, lean_object* v_toMul_650_, lean_object* v_toAddCommMonoid_651_, lean_object* v___f_652_, lean_object* v_j_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = lp_GRH_New_U_conj___redArg___lam__3(v_val_648_, v_inst_649_, v_toMul_650_, v_toAddCommMonoid_651_, v___f_652_, v_j_653_);
lean_dec_ref(v_toAddCommMonoid_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__4(lean_object* v_inv_655_, lean_object* v_val_656_, lean_object* v_val_657_, lean_object* v_inst_658_, lean_object* v_toMul_659_, lean_object* v_toAddCommMonoid_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_663_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__0), 3, 2);
lean_closure_set(v___f_663_, 0, v_inv_655_);
lean_closure_set(v___f_663_, 1, v___y_662_);
v___f_664_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__1), 3, 2);
lean_closure_set(v___f_664_, 0, v_val_656_);
lean_closure_set(v___f_664_, 1, v___y_661_);
lean_inc_ref(v_toAddCommMonoid_660_);
lean_inc(v_toMul_659_);
lean_inc(v_inst_658_);
v___f_665_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_665_, 0, v_val_657_);
lean_closure_set(v___f_665_, 1, v_inst_658_);
lean_closure_set(v___f_665_, 2, v_toMul_659_);
lean_closure_set(v___f_665_, 3, v_toAddCommMonoid_660_);
lean_closure_set(v___f_665_, 4, v___f_664_);
v___x_666_ = lp_mathlib_dotProduct___redArg(v_inst_658_, v_toMul_659_, v_toAddCommMonoid_660_, v___f_665_, v___f_663_);
lean_dec_ref(v_toAddCommMonoid_660_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__6(lean_object* v_inv_667_, lean_object* v_j_668_, lean_object* v_j_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = lean_apply_2(v_inv_667_, v_j_668_, v_j_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__5(lean_object* v_inv_671_, lean_object* v_inst_672_, lean_object* v_toMul_673_, lean_object* v_toAddCommMonoid_674_, lean_object* v___f_675_, lean_object* v_j_676_){
_start:
{
lean_object* v___f_677_; lean_object* v___x_678_; 
v___f_677_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__6), 3, 2);
lean_closure_set(v___f_677_, 0, v_inv_671_);
lean_closure_set(v___f_677_, 1, v_j_676_);
v___x_678_ = lp_mathlib_dotProduct___redArg(v_inst_672_, v_toMul_673_, v_toAddCommMonoid_674_, v___f_677_, v___f_675_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__5___boxed(lean_object* v_inv_679_, lean_object* v_inst_680_, lean_object* v_toMul_681_, lean_object* v_toAddCommMonoid_682_, lean_object* v___f_683_, lean_object* v_j_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = lp_GRH_New_U_conj___redArg___lam__5(v_inv_679_, v_inst_680_, v_toMul_681_, v_toAddCommMonoid_682_, v___f_683_, v_j_684_);
lean_dec_ref(v_toAddCommMonoid_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__8(lean_object* v_inv_686_, lean_object* v_inv_687_, lean_object* v_inst_688_, lean_object* v_toMul_689_, lean_object* v_toAddCommMonoid_690_, lean_object* v_val_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_694_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__0), 3, 2);
lean_closure_set(v___f_694_, 0, v_inv_686_);
lean_closure_set(v___f_694_, 1, v___y_693_);
lean_inc_ref(v_toAddCommMonoid_690_);
lean_inc(v_toMul_689_);
lean_inc(v_inst_688_);
v___f_695_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_695_, 0, v_inv_687_);
lean_closure_set(v___f_695_, 1, v_inst_688_);
lean_closure_set(v___f_695_, 2, v_toMul_689_);
lean_closure_set(v___f_695_, 3, v_toAddCommMonoid_690_);
lean_closure_set(v___f_695_, 4, v___f_694_);
v___f_696_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__1), 3, 2);
lean_closure_set(v___f_696_, 0, v_val_691_);
lean_closure_set(v___f_696_, 1, v___y_692_);
v___x_697_ = lp_mathlib_dotProduct___redArg(v_inst_688_, v_toMul_689_, v_toAddCommMonoid_690_, v___f_696_, v___f_695_);
lean_dec_ref(v_toAddCommMonoid_690_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__7(lean_object* v_x_698_, lean_object* v_toSemiring_699_, lean_object* v_inst_700_, lean_object* v_g_701_){
_start:
{
lean_object* v_val_702_; lean_object* v_inv_703_; lean_object* v_val_704_; lean_object* v_inv_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_718_; 
v_val_702_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_val_702_);
v_inv_703_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_inv_703_);
lean_dec_ref(v_x_698_);
v_val_704_ = lean_ctor_get(v_g_701_, 0);
v_inv_705_ = lean_ctor_get(v_g_701_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_g_701_);
if (v_isSharedCheck_718_ == 0)
{
v___x_707_ = v_g_701_;
v_isShared_708_ = v_isSharedCheck_718_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_inv_705_);
lean_inc(v_val_704_);
lean_dec(v_g_701_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_718_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v_toAddCommMonoid_710_; lean_object* v___x_711_; lean_object* v_toMul_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___x_716_; 
v___x_709_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_699_);
v_toAddCommMonoid_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref_n(v_toAddCommMonoid_710_, 2);
v___x_711_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_709_);
v_toMul_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_n(v_toMul_712_, 2);
lean_dec_ref(v___x_711_);
lean_inc(v_inst_700_);
lean_inc(v_val_702_);
lean_inc(v_inv_703_);
v___f_713_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__4), 8, 6);
lean_closure_set(v___f_713_, 0, v_inv_703_);
lean_closure_set(v___f_713_, 1, v_val_702_);
lean_closure_set(v___f_713_, 2, v_val_704_);
lean_closure_set(v___f_713_, 3, v_inst_700_);
lean_closure_set(v___f_713_, 4, v_toMul_712_);
lean_closure_set(v___f_713_, 5, v_toAddCommMonoid_710_);
v___f_714_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__8), 8, 6);
lean_closure_set(v___f_714_, 0, v_inv_703_);
lean_closure_set(v___f_714_, 1, v_inv_705_);
lean_closure_set(v___f_714_, 2, v_inst_700_);
lean_closure_set(v___f_714_, 3, v_toMul_712_);
lean_closure_set(v___f_714_, 4, v_toAddCommMonoid_710_);
lean_closure_set(v___f_714_, 5, v_val_702_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___f_714_);
lean_ctor_set(v___x_707_, 0, v___f_713_);
v___x_716_ = v___x_707_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___f_713_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___f_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__7___boxed(lean_object* v_x_719_, lean_object* v_toSemiring_720_, lean_object* v_inst_721_, lean_object* v_g_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = lp_GRH_New_U_conj___redArg___lam__7(v_x_719_, v_toSemiring_720_, v_inst_721_, v_g_722_);
lean_dec_ref(v_toSemiring_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__9(lean_object* v_val_724_, lean_object* v___y_725_, lean_object* v_j_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_apply_2(v_val_724_, v_j_726_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__12(lean_object* v_inv_728_, lean_object* v___y_729_, lean_object* v_j_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_apply_2(v_inv_728_, v___y_729_, v_j_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__10(lean_object* v_val_732_, lean_object* v_inv_733_, lean_object* v_inst_734_, lean_object* v_toMul_735_, lean_object* v_toAddCommMonoid_736_, lean_object* v_inv_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v___f_740_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__9), 3, 2);
lean_closure_set(v___f_740_, 0, v_val_732_);
lean_closure_set(v___f_740_, 1, v___y_739_);
lean_inc_ref(v_toAddCommMonoid_736_);
lean_inc(v_toMul_735_);
lean_inc(v_inst_734_);
v___f_741_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_741_, 0, v_inv_733_);
lean_closure_set(v___f_741_, 1, v_inst_734_);
lean_closure_set(v___f_741_, 2, v_toMul_735_);
lean_closure_set(v___f_741_, 3, v_toAddCommMonoid_736_);
lean_closure_set(v___f_741_, 4, v___f_740_);
v___f_742_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__12), 3, 2);
lean_closure_set(v___f_742_, 0, v_inv_737_);
lean_closure_set(v___f_742_, 1, v___y_738_);
v___x_743_ = lp_mathlib_dotProduct___redArg(v_inst_734_, v_toMul_735_, v_toAddCommMonoid_736_, v___f_742_, v___f_741_);
lean_dec_ref(v_toAddCommMonoid_736_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__16(lean_object* v_val_744_, lean_object* v_inv_745_, lean_object* v_val_746_, lean_object* v_inst_747_, lean_object* v_toMul_748_, lean_object* v_toAddCommMonoid_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v___f_752_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__9), 3, 2);
lean_closure_set(v___f_752_, 0, v_val_744_);
lean_closure_set(v___f_752_, 1, v___y_751_);
v___f_753_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__12), 3, 2);
lean_closure_set(v___f_753_, 0, v_inv_745_);
lean_closure_set(v___f_753_, 1, v___y_750_);
lean_inc_ref(v_toAddCommMonoid_749_);
lean_inc(v_toMul_748_);
lean_inc(v_inst_747_);
v___f_754_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_754_, 0, v_val_746_);
lean_closure_set(v___f_754_, 1, v_inst_747_);
lean_closure_set(v___f_754_, 2, v_toMul_748_);
lean_closure_set(v___f_754_, 3, v_toAddCommMonoid_749_);
lean_closure_set(v___f_754_, 4, v___f_753_);
v___x_755_ = lp_mathlib_dotProduct___redArg(v_inst_747_, v_toMul_748_, v_toAddCommMonoid_749_, v___f_754_, v___f_752_);
lean_dec_ref(v_toAddCommMonoid_749_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__11(lean_object* v_x_756_, lean_object* v_toSemiring_757_, lean_object* v_inst_758_, lean_object* v_g_759_){
_start:
{
lean_object* v_val_760_; lean_object* v_inv_761_; lean_object* v_val_762_; lean_object* v_inv_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_776_; 
v_val_760_ = lean_ctor_get(v_x_756_, 0);
lean_inc(v_val_760_);
v_inv_761_ = lean_ctor_get(v_x_756_, 1);
lean_inc(v_inv_761_);
lean_dec_ref(v_x_756_);
v_val_762_ = lean_ctor_get(v_g_759_, 0);
v_inv_763_ = lean_ctor_get(v_g_759_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_g_759_);
if (v_isSharedCheck_776_ == 0)
{
v___x_765_ = v_g_759_;
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_inv_763_);
lean_inc(v_val_762_);
lean_dec(v_g_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v_toAddCommMonoid_768_; lean_object* v___x_769_; lean_object* v_toMul_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_774_; 
v___x_767_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_757_);
v_toAddCommMonoid_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_ref_n(v_toAddCommMonoid_768_, 2);
v___x_769_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_767_);
v_toMul_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_toMul_770_, 2);
lean_dec_ref(v___x_769_);
lean_inc(v_inv_761_);
lean_inc(v_inst_758_);
lean_inc(v_val_760_);
v___f_771_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__10), 8, 6);
lean_closure_set(v___f_771_, 0, v_val_760_);
lean_closure_set(v___f_771_, 1, v_inv_763_);
lean_closure_set(v___f_771_, 2, v_inst_758_);
lean_closure_set(v___f_771_, 3, v_toMul_770_);
lean_closure_set(v___f_771_, 4, v_toAddCommMonoid_768_);
lean_closure_set(v___f_771_, 5, v_inv_761_);
v___f_772_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__16), 8, 6);
lean_closure_set(v___f_772_, 0, v_val_760_);
lean_closure_set(v___f_772_, 1, v_inv_761_);
lean_closure_set(v___f_772_, 2, v_val_762_);
lean_closure_set(v___f_772_, 3, v_inst_758_);
lean_closure_set(v___f_772_, 4, v_toMul_770_);
lean_closure_set(v___f_772_, 5, v_toAddCommMonoid_768_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___f_771_);
lean_ctor_set(v___x_765_, 0, v___f_772_);
v___x_774_ = v___x_765_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___f_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___f_771_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg___lam__11___boxed(lean_object* v_x_777_, lean_object* v_toSemiring_778_, lean_object* v_inst_779_, lean_object* v_g_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = lp_GRH_New_U_conj___redArg___lam__11(v_x_777_, v_toSemiring_778_, v_inst_779_, v_g_780_);
lean_dec_ref(v_toSemiring_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___redArg(lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_toSemiring_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; 
v_toSemiring_785_ = lean_ctor_get(v_inst_783_, 0);
lean_inc_ref_n(v_toSemiring_785_, 2);
lean_dec_ref(v_inst_783_);
lean_inc(v_inst_782_);
lean_inc_ref(v_x_784_);
v___f_786_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_786_, 0, v_x_784_);
lean_closure_set(v___f_786_, 1, v_toSemiring_785_);
lean_closure_set(v___f_786_, 2, v_inst_782_);
v___f_787_ = lean_alloc_closure((void*)(lp_GRH_New_U_conj___redArg___lam__11___boxed), 4, 3);
lean_closure_set(v___f_787_, 0, v_x_784_);
lean_closure_set(v___f_787_, 1, v_toSemiring_785_);
lean_closure_set(v___f_787_, 2, v_inst_782_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___f_786_);
lean_ctor_set(v___x_788_, 1, v___f_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj(lean_object* v_n_789_, lean_object* v_R_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_x_795_, lean_object* v_J_796_, lean_object* v_J_x27_797_, lean_object* v_h_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lp_GRH_New_U_conj___redArg(v_inst_791_, v_inst_792_, v_x_795_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_conj___boxed(lean_object* v_n_800_, lean_object* v_R_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_x_806_, lean_object* v_J_807_, lean_object* v_J_x27_808_, lean_object* v_h_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = lp_GRH_New_U_conj(v_n_800_, v_R_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_inst_805_, v_x_806_, v_J_807_, v_J_x27_808_, v_h_809_);
lean_dec(v_J_x27_808_);
lean_dec(v_J_807_);
lean_dec_ref(v_inst_805_);
lean_dec(v_inst_804_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_det___redArg___lam__0(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_g_814_){
_start:
{
lean_object* v_val_815_; lean_object* v___x_40__overap_816_; lean_object* v___x_817_; 
v_val_815_ = lean_ctor_get(v_g_814_, 0);
lean_inc(v_val_815_);
lean_dec_ref(v_g_814_);
v___x_40__overap_816_ = lp_mathlib_Matrix_detRowAlternating___redArg(v_inst_811_, v_inst_812_, v_inst_813_);
v___x_817_ = lean_apply_1(v___x_40__overap_816_, v_val_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_det___redArg(lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_){
_start:
{
lean_object* v___f_821_; 
v___f_821_ = lean_alloc_closure((void*)(lp_GRH_New_U_det___redArg___lam__0), 4, 3);
lean_closure_set(v___f_821_, 0, v_inst_820_);
lean_closure_set(v___f_821_, 1, v_inst_818_);
lean_closure_set(v___f_821_, 2, v_inst_819_);
return v___f_821_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_det(lean_object* v_n_822_, lean_object* v_R_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_J_828_, lean_object* v_hJ_829_){
_start:
{
lean_object* v___f_830_; 
v___f_830_ = lean_alloc_closure((void*)(lp_GRH_New_U_det___redArg___lam__0), 4, 3);
lean_closure_set(v___f_830_, 0, v_inst_827_);
lean_closure_set(v___f_830_, 1, v_inst_824_);
lean_closure_set(v___f_830_, 2, v_inst_825_);
return v___f_830_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_det___boxed(lean_object* v_n_831_, lean_object* v_R_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_J_837_, lean_object* v_hJ_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = lp_GRH_New_U_det(v_n_831_, v_R_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_J_837_, v_hJ_838_);
lean_dec(v_J_837_);
lean_dec(v_inst_835_);
return v_res_839_;
}
}
static lean_object* _init_lp_GRH_New_U_continuous__map___auto__1(void){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22, &lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22_once, _init_lp_GRH_IsCompact_image__of__continuous___auto__1___closed__22);
return v___x_840_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Groups_CongruenceSubgroups(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Base(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_IsCompact_preimage__val___auto__1 = _init_lp_GRH_IsCompact_preimage__val___auto__1();
lean_mark_persistent(lp_GRH_IsCompact_preimage__val___auto__1);
lp_GRH_IsCompact_image__of__continuous___auto__1 = _init_lp_GRH_IsCompact_image__of__continuous___auto__1();
lean_mark_persistent(lp_GRH_IsCompact_image__of__continuous___auto__1);
lp_GRH_IsOpen_preimage__of__continuous___auto__1 = _init_lp_GRH_IsOpen_preimage__of__continuous___auto__1();
lean_mark_persistent(lp_GRH_IsOpen_preimage__of__continuous___auto__1);
lp_GRH_IsClosed_preimage__of__continuous___auto__1 = _init_lp_GRH_IsClosed_preimage__of__continuous___auto__1();
lean_mark_persistent(lp_GRH_IsClosed_preimage__of__continuous___auto__1);
lp_GRH_IsCompact_integrableOn___auto__1 = _init_lp_GRH_IsCompact_integrableOn___auto__1();
lean_mark_persistent(lp_GRH_IsCompact_integrableOn___auto__1);
lp_GRH_HasCompactSupport_integrable___auto__1 = _init_lp_GRH_HasCompactSupport_integrable___auto__1();
lean_mark_persistent(lp_GRH_HasCompactSupport_integrable___auto__1);
lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1 = _init_lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1();
lean_mark_persistent(lp_GRH_New_DiscreteSeries_integrable__of__compactSpace___auto__1);
lp_GRH_New_U_map___auto__1 = _init_lp_GRH_New_U_map___auto__1();
lean_mark_persistent(lp_GRH_New_U_map___auto__1);
lp_GRH_New_U_map___auto__3 = _init_lp_GRH_New_U_map___auto__3();
lean_mark_persistent(lp_GRH_New_U_map___auto__3);
lp_GRH_New_U_continuous__map___auto__1 = _init_lp_GRH_New_U_continuous__map___auto__1();
lean_mark_persistent(lp_GRH_New_U_continuous__map___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
