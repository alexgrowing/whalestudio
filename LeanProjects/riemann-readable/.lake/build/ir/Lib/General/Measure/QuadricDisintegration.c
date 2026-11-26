// Lean compiler output
// Module: Lib.General.Measure.QuadricDisintegration
// Imports: public import Init public meta import Init public import Lib.Adelic.Witt.WittTheorem
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lp_mathlib_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_instTraceOneOfCharZero___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_instTraceOneOfCharZero(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_instTraceOneOfCharZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_skewPart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_skewPart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_hermitianMul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_hermitianMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_hermitianMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_planeSumGram___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Floors_planeSumGram___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_planeSumGram___redArg___closed__0;
static const lean_closure_object lp_GRH_New_Floors_planeSumGram___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Matrix_vecEmpty___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Floors_planeSumGram___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Floors_planeSumGram___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_planeSumGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_planeSumGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11_value;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__13;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__14_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__15_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value_aux_0),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value_aux_1),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value_aux_2),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "IsHermitian.apply"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__17 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__17_value;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__18;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__19;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "IsHermitian"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__20 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__20_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(23, 14, 243, 80, 220, 92, 43, 92)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__21_value_aux_0),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 60, 101, 4, 141, 70, 84, 130)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__21 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__21_value;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__23;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "IsHermitianUnit.conjTranspose_eq"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__24 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__24_value;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__26;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "IsHermitianUnit"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__27 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__27_value;
static const lean_string_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "conjTranspose_eq"};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__28 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__28_value;
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(180, 25, 61, 39, 38, 163, 203, 25)}};
static const lean_ctor_object lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__29_value_aux_0),((lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(95, 26, 7, 49, 9, 16, 118, 244)}};
static const lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__29 = (const lean_object*)&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__29_value;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__32;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__33;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__34;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__35;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__36;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__37;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__38;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__39;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__40;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__41;
static lean_once_cell_t lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__42;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_instTraceOneOfCharZero___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_toInv_6_; lean_object* v___x_7_; lean_object* v_toRing_8_; lean_object* v___x_9_; lean_object* v_toAddMonoidWithOne_10_; lean_object* v_toNatCast_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_2_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_3_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_2_);
lean_dec_ref(v___x_2_);
v___x_4_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_3_);
v___x_5_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_4_);
lean_dec_ref(v___x_4_);
v_toInv_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_toInv_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v_toRing_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_toRing_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_8_);
v_toAddMonoidWithOne_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc_ref(v_toAddMonoidWithOne_10_);
lean_dec_ref(v___x_9_);
v_toNatCast_11_ = lean_ctor_get(v_toAddMonoidWithOne_10_, 0);
lean_inc(v_toNatCast_11_);
lean_dec_ref(v_toAddMonoidWithOne_10_);
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lean_apply_1(v_toNatCast_11_, v___x_12_);
v___x_14_ = lean_apply_1(v_toInv_6_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_instTraceOneOfCharZero(lean_object* v_A_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_GRH_New_Floors_instTraceOneOfCharZero___redArg(v_inst_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_instTraceOneOfCharZero___boxed(lean_object* v_A_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_Floors_instTraceOneOfCharZero(v_A_20_, v_inst_21_, v_inst_22_, v_inst_23_);
lean_dec(v_inst_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_skewPart___redArg(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_toSub_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_28_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_25_);
v___x_29_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_28_);
lean_dec_ref(v___x_28_);
v_toSub_30_ = lean_ctor_get(v___x_29_, 2);
lean_inc(v_toSub_30_);
lean_dec_ref(v___x_29_);
lean_inc(v_x_27_);
v___x_31_ = lean_apply_1(v_inst_26_, v_x_27_);
v___x_32_ = lean_apply_2(v_toSub_30_, v_x_27_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_skewPart(lean_object* v_A_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v_toSub_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_37_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_34_);
v___x_38_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_37_);
lean_dec_ref(v___x_37_);
v_toSub_39_ = lean_ctor_get(v___x_38_, 2);
lean_inc(v_toSub_39_);
lean_dec_ref(v___x_38_);
lean_inc(v_x_36_);
v___x_40_ = lean_apply_1(v_inst_35_, v_x_36_);
v___x_41_ = lean_apply_2(v_toSub_39_, v_x_36_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_hermitianMul___redArg(lean_object* v_inst_42_, lean_object* v_x_43_, lean_object* v_00_u03b2_44_){
_start:
{
lean_object* v_toSemiring_45_; lean_object* v___x_46_; lean_object* v_toMul_47_; lean_object* v___x_48_; 
v_toSemiring_45_ = lean_ctor_get(v_inst_42_, 0);
lean_inc_ref(v_toSemiring_45_);
lean_dec_ref(v_inst_42_);
v___x_46_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_45_);
v_toMul_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_toMul_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_apply_2(v_toMul_47_, v_x_43_, v_00_u03b2_44_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_hermitianMul(lean_object* v_A_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_x_52_, lean_object* v_hx_53_, lean_object* v_00_u03b2_54_){
_start:
{
lean_object* v_toSemiring_55_; lean_object* v___x_56_; lean_object* v_toMul_57_; lean_object* v___x_58_; 
v_toSemiring_55_ = lean_ctor_get(v_inst_50_, 0);
lean_inc_ref(v_toSemiring_55_);
lean_dec_ref(v_inst_50_);
v___x_56_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_55_);
v_toMul_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_toMul_57_);
lean_dec_ref(v___x_56_);
v___x_58_ = lean_apply_2(v_toMul_57_, v_x_52_, v_00_u03b2_54_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_hermitianMul___boxed(lean_object* v_A_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_x_62_, lean_object* v_hx_63_, lean_object* v_00_u03b2_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_GRH_New_Floors_hermitianMul(v_A_59_, v_inst_60_, v_inst_61_, v_x_62_, v_hx_63_, v_00_u03b2_64_);
lean_dec(v_inst_61_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_planeSumGram___redArg___lam__0(lean_object* v___x_66_, lean_object* v___x_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_toFun_70_; lean_object* v___x_71_; 
v_toFun_70_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_toFun_70_);
lean_dec_ref(v___x_66_);
v___x_71_ = lean_apply_3(v_toFun_70_, v___x_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
static lean_object* _init_lp_GRH_New_Floors_planeSumGram___redArg___closed__0(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_mathlib_Equiv_refl___redArg();
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_planeSumGram___redArg(lean_object* v_inst_74_, lean_object* v_T_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_toSemiring_78_; lean_object* v___x_79_; lean_object* v_toZero_80_; lean_object* v___x_81_; lean_object* v_toAddMonoidWithOne_82_; lean_object* v_toOne_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_toSemiring_78_ = lean_ctor_get(v_inst_74_, 0);
lean_inc_ref(v_toSemiring_78_);
v___x_79_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_78_);
v_toZero_80_ = lean_ctor_get(v___x_79_, 1);
lean_inc_n(v_toZero_80_, 3);
lean_dec_ref(v___x_79_);
v___x_81_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_74_);
v_toAddMonoidWithOne_82_ = lean_ctor_get(v___x_81_, 1);
lean_inc_ref(v_toAddMonoidWithOne_82_);
lean_dec_ref(v___x_81_);
v_toOne_83_ = lean_ctor_get(v_toAddMonoidWithOne_82_, 2);
lean_inc_n(v_toOne_83_, 2);
lean_dec_ref(v_toAddMonoidWithOne_82_);
v___x_84_ = lean_obj_once(&lp_GRH_New_Floors_planeSumGram___redArg___closed__0, &lp_GRH_New_Floors_planeSumGram___redArg___closed__0_once, _init_lp_GRH_New_Floors_planeSumGram___redArg___closed__0);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = ((lean_object*)(lp_GRH_New_Floors_planeSumGram___redArg___closed__1));
v___x_88_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_88_, 0, lean_box(0));
lean_closure_set(v___x_88_, 1, v___x_86_);
lean_closure_set(v___x_88_, 2, v_toOne_83_);
lean_closure_set(v___x_88_, 3, v___x_87_);
v___x_89_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_89_, 0, lean_box(0));
lean_closure_set(v___x_89_, 1, v___x_85_);
lean_closure_set(v___x_89_, 2, v_toZero_80_);
lean_closure_set(v___x_89_, 3, v___x_88_);
v___x_90_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_90_, 0, lean_box(0));
lean_closure_set(v___x_90_, 1, v___x_86_);
lean_closure_set(v___x_90_, 2, v_toZero_80_);
lean_closure_set(v___x_90_, 3, v___x_87_);
v___x_91_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, v___x_85_);
lean_closure_set(v___x_91_, 2, v_toOne_83_);
lean_closure_set(v___x_91_, 3, v___x_90_);
v___x_92_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, v___x_86_);
lean_closure_set(v___x_92_, 2, v___x_91_);
lean_closure_set(v___x_92_, 3, v___x_87_);
v___x_93_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_93_, 0, lean_box(0));
lean_closure_set(v___x_93_, 1, v___x_85_);
lean_closure_set(v___x_93_, 2, v___x_89_);
lean_closure_set(v___x_93_, 3, v___x_92_);
v___f_94_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_planeSumGram___redArg___lam__0), 4, 2);
lean_closure_set(v___f_94_, 0, v___x_84_);
lean_closure_set(v___f_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_95_, 0, lean_box(0));
lean_closure_set(v___x_95_, 1, lean_box(0));
lean_closure_set(v___x_95_, 2, lean_box(0));
lean_closure_set(v___x_95_, 3, v_toZero_80_);
lean_inc_ref(v___x_95_);
v___x_96_ = lp_mathlib_Matrix_fromBlocks___redArg(v___f_94_, v___x_95_, v___x_95_, v_T_75_, v_a_76_, v_a_77_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_planeSumGram(lean_object* v_A_97_, lean_object* v_inst_98_, lean_object* v_00_u03b9_99_, lean_object* v_T_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_toSemiring_103_; lean_object* v___x_104_; lean_object* v_toZero_105_; lean_object* v___x_106_; lean_object* v_toAddMonoidWithOne_107_; lean_object* v_toOne_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_toSemiring_103_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toSemiring_103_);
v___x_104_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_103_);
v_toZero_105_ = lean_ctor_get(v___x_104_, 1);
lean_inc_n(v_toZero_105_, 3);
lean_dec_ref(v___x_104_);
v___x_106_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_98_);
v_toAddMonoidWithOne_107_ = lean_ctor_get(v___x_106_, 1);
lean_inc_ref(v_toAddMonoidWithOne_107_);
lean_dec_ref(v___x_106_);
v_toOne_108_ = lean_ctor_get(v_toAddMonoidWithOne_107_, 2);
lean_inc_n(v_toOne_108_, 2);
lean_dec_ref(v_toAddMonoidWithOne_107_);
v___x_109_ = lean_obj_once(&lp_GRH_New_Floors_planeSumGram___redArg___closed__0, &lp_GRH_New_Floors_planeSumGram___redArg___closed__0_once, _init_lp_GRH_New_Floors_planeSumGram___redArg___closed__0);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = ((lean_object*)(lp_GRH_New_Floors_planeSumGram___redArg___closed__1));
v___x_113_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_113_, 0, lean_box(0));
lean_closure_set(v___x_113_, 1, v___x_111_);
lean_closure_set(v___x_113_, 2, v_toOne_108_);
lean_closure_set(v___x_113_, 3, v___x_112_);
v___x_114_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_114_, 0, lean_box(0));
lean_closure_set(v___x_114_, 1, v___x_110_);
lean_closure_set(v___x_114_, 2, v_toZero_105_);
lean_closure_set(v___x_114_, 3, v___x_113_);
v___x_115_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_115_, 0, lean_box(0));
lean_closure_set(v___x_115_, 1, v___x_111_);
lean_closure_set(v___x_115_, 2, v_toZero_105_);
lean_closure_set(v___x_115_, 3, v___x_112_);
v___x_116_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, v___x_110_);
lean_closure_set(v___x_116_, 2, v_toOne_108_);
lean_closure_set(v___x_116_, 3, v___x_115_);
v___x_117_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_117_, 0, lean_box(0));
lean_closure_set(v___x_117_, 1, v___x_111_);
lean_closure_set(v___x_117_, 2, v___x_116_);
lean_closure_set(v___x_117_, 3, v___x_112_);
v___x_118_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_118_, 0, lean_box(0));
lean_closure_set(v___x_118_, 1, v___x_110_);
lean_closure_set(v___x_118_, 2, v___x_114_);
lean_closure_set(v___x_118_, 3, v___x_117_);
v___f_119_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_planeSumGram___redArg___lam__0), 4, 2);
lean_closure_set(v___f_119_, 0, v___x_109_);
lean_closure_set(v___f_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_120_, 0, lean_box(0));
lean_closure_set(v___x_120_, 1, lean_box(0));
lean_closure_set(v___x_120_, 2, lean_box(0));
lean_closure_set(v___x_120_, 3, v_toZero_105_);
lean_inc_ref(v___x_120_);
v___x_121_ = lp_mathlib_Matrix_fromBlocks___redArg(v___f_119_, v___x_120_, v___x_120_, v_T_100_, v_a_101_, v_a_102_);
return v___x_121_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__12(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__10));
v___x_149_ = l_Lean_mkAtom(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__13(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__12, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__12_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__12);
v___x_151_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5));
v___x_152_ = lean_array_push(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__18(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__17));
v___x_162_ = lean_string_utf8_byte_size(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__19(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__18, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__18_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__18);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__17));
v___x_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
return v___x_166_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__22(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = lean_box(0);
v___x_172_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__21));
v___x_173_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__19, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__19_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__19);
v___x_174_ = lean_box(2);
v___x_175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_172_);
lean_ctor_set(v___x_175_, 3, v___x_171_);
return v___x_175_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__23(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__22, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__22_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__22);
v___x_177_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5));
v___x_178_ = lean_array_push(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__25(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__24));
v___x_181_ = lean_string_utf8_byte_size(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__26(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__25, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__25_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__25);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__24));
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__30(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_191_ = lean_box(0);
v___x_192_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__29));
v___x_193_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__26, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__26_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__26);
v___x_194_ = lean_box(2);
v___x_195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
lean_ctor_set(v___x_195_, 3, v___x_191_);
return v___x_195_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__31(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__30, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__30_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__30);
v___x_197_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5));
v___x_198_ = lean_array_push(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__32(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__31, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__31_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__31);
v___x_200_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__9));
v___x_201_ = lean_box(2);
v___x_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_199_);
return v___x_202_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__33(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__32, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__32_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__32);
v___x_204_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__23, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__23_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__23);
v___x_205_ = lean_array_push(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__34(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__33, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__33_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__33);
v___x_207_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__16));
v___x_208_ = lean_box(2);
v___x_209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
return v___x_209_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__35(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__34, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__34_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__34);
v___x_211_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__13, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__13_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__13);
v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__36(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__35, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__35_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__35);
v___x_214_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__11));
v___x_215_ = lean_box(2);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
return v___x_216_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__37(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__36, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__36_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__36);
v___x_218_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5));
v___x_219_ = lean_array_push(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__38(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__37, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__37_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__37);
v___x_221_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__9));
v___x_222_ = lean_box(2);
v___x_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_220_);
return v___x_223_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__39(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__38, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__38_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__38);
v___x_225_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5));
v___x_226_ = lean_array_push(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__40(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__39, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__39_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__39);
v___x_228_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__7));
v___x_229_ = lean_box(2);
v___x_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
return v___x_230_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__41(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__40, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__40_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__40);
v___x_232_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__5));
v___x_233_ = lean_array_push(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__42(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_234_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__41, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__41_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__41);
v___x_235_ = ((lean_object*)(lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__4));
v___x_236_ = lean_box(2);
v___x_237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_234_);
return v___x_237_;
}
}
static lean_object* _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__42, &lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__42_once, _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1___closed__42);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul___redArg(lean_object* v_inst_239_, lean_object* v_P_240_, lean_object* v_00_u0393_241_){
_start:
{
lean_object* v_toSemiring_242_; lean_object* v___x_243_; lean_object* v_skewUnit_244_; lean_object* v_toMul_245_; lean_object* v_val_246_; lean_object* v___x_247_; 
v_toSemiring_242_ = lean_ctor_get(v_inst_239_, 0);
lean_inc_ref(v_toSemiring_242_);
lean_dec_ref(v_inst_239_);
v___x_243_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_242_);
v_skewUnit_244_ = lean_ctor_get(v_P_240_, 1);
lean_inc_ref(v_skewUnit_244_);
lean_dec_ref(v_P_240_);
v_toMul_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_toMul_245_);
lean_dec_ref(v___x_243_);
v_val_246_ = lean_ctor_get(v_skewUnit_244_, 0);
lean_inc(v_val_246_);
lean_dec_ref(v_skewUnit_244_);
v___x_247_ = lean_apply_2(v_toMul_245_, v_val_246_, v_00_u0393_241_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul(lean_object* v_A_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_P_253_, lean_object* v_00_u0393_254_, lean_object* v_h_u0393_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lp_GRH_New_Floors_Place_skewUnitMul___redArg(v_inst_249_, v_P_253_, v_00_u0393_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_skewUnitMul___boxed(lean_object* v_A_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_P_262_, lean_object* v_00_u0393_263_, lean_object* v_h_u0393_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = lp_GRH_New_Floors_Place_skewUnitMul(v_A_257_, v_inst_258_, v_inst_259_, v_inst_260_, v_inst_261_, v_P_262_, v_00_u0393_263_, v_h_u0393_264_);
lean_dec_ref(v_inst_261_);
lean_dec(v_inst_259_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter___redArg(lean_object* v_x_266_, lean_object* v_h__1_267_){
_start:
{
lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_272_; 
v_fst_268_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v_x_266_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v_x_266_);
v_fst_270_ = lean_ctor_get(v_fst_268_, 0);
lean_inc(v_fst_270_);
v_snd_271_ = lean_ctor_get(v_fst_268_, 1);
lean_inc(v_snd_271_);
lean_dec(v_fst_268_);
v___x_272_ = lean_apply_3(v_h__1_267_, v_fst_270_, v_snd_271_, v_snd_269_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter(lean_object* v_A_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_00_u03b9_276_, lean_object* v_motive_277_, lean_object* v_x_278_, lean_object* v_h__1_279_){
_start:
{
lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v___x_284_; 
v_fst_280_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_fst_280_);
v_snd_281_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_snd_281_);
lean_dec_ref(v_x_278_);
v_fst_282_ = lean_ctor_get(v_fst_280_, 0);
lean_inc(v_fst_282_);
v_snd_283_ = lean_ctor_get(v_fst_280_, 1);
lean_inc(v_snd_283_);
lean_dec(v_fst_280_);
v___x_284_ = lean_apply_3(v_h__1_279_, v_fst_282_, v_snd_283_, v_snd_281_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter___boxed(lean_object* v_A_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_00_u03b9_288_, lean_object* v_motive_289_, lean_object* v_x_290_, lean_object* v_h__1_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_GRH___private_Lib_General_Measure_QuadricDisintegration_0__New_Floors_Place_flatChart_match__1_splitter(v_A_285_, v_inst_286_, v_inst_287_, v_00_u03b9_288_, v_motive_289_, v_x_290_, v_h__1_291_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
return v_res_292_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Witt_WittTheorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Measure_QuadricDisintegration(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Witt_WittTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Floors_Place_skewUnitMul___auto__1 = _init_lp_GRH_New_Floors_Place_skewUnitMul___auto__1();
lean_mark_persistent(lp_GRH_New_Floors_Place_skewUnitMul___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
