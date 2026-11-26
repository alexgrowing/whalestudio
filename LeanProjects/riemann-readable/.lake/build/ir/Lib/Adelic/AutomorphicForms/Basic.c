// Lean compiler output
// Module: Lib.Adelic.AutomorphicForms.Basic
// Imports: public import Init public meta import Init public import Lib.Adelic.Reduction.DefiniteClassSums
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddMonoid;
lean_object* lp_mathlib_NSMul_toSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddGroup;
lean_object* lp_mathlib_ZSMul_toSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Mathlib"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__10_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__11_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunProp"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__12 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__12_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funPropTacStx"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__13 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__13_value;
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(118, 213, 161, 2, 73, 184, 31, 228)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value_aux_0),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(210, 10, 180, 159, 248, 97, 218, 144)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value_aux_1),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 118, 4, 116, 28, 199, 219)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value_aux_2),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(146, 162, 46, 139, 110, 137, 217, 136)}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14_value;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fun_prop"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__15_value;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__16;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__17;
static const lean_string_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__18 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__18_value;
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value_aux_0),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value_aux_1),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value_aux_2),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19_value;
static const lean_ctor_object lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__20 = (const lean_object*)&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__20_value;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__26;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__27;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__28;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__32;
LEAN_EXPORT lean_object* lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__0 = (const lean_object*)&lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__0_value)} };
static const lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__1 = (const lean_object*)&lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__16(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__15));
v___x_32_ = l_Lean_mkAtom(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__17(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__16, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__16_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__16);
v___x_34_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5));
v___x_35_ = lean_array_push(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__21(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__20));
v___x_47_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5));
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__22(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__21, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__21_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__21);
v___x_50_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__19));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__23(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__22, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__22_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__22);
v___x_54_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__17, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__17_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__17);
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__24(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__20));
v___x_57_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__23, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__23_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__23);
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__25(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__20));
v___x_60_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__24, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__24_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__24);
v___x_61_ = lean_array_push(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__26(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__25, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__25_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__25);
v___x_63_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__14));
v___x_64_ = lean_box(2);
v___x_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__27(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__26, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__26_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__26);
v___x_67_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5));
v___x_68_ = lean_array_push(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__28(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__27, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__27_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__27);
v___x_70_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__9));
v___x_71_ = lean_box(2);
v___x_72_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__29(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__28, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__28_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__28);
v___x_74_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5));
v___x_75_ = lean_array_push(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__30(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__29, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__29_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__29);
v___x_77_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__7));
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__31(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__30, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__30_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__30);
v___x_81_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__5));
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__32(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__31, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__31_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__31);
v___x_84_ = ((lean_object*)(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__4));
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__32, &lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__32_once, _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1___closed__32);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule___redArg(){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_GRH_New_Space_formSubmodule___redArg();
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule(lean_object* v_E_92_, lean_object* v_n_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_s_98_, lean_object* v_V_99_, lean_object* v_e_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(0);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_formSubmodule___boxed(lean_object* v_E_102_, lean_object* v_n_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_s_108_, lean_object* v_V_109_, lean_object* v_e_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_GRH_New_Space_formSubmodule(v_E_102_, v_n_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_inst_107_, v_s_108_, v_V_109_, v_e_110_);
lean_dec_ref(v_e_110_);
lean_dec_ref(v_V_109_);
lean_dec_ref(v_s_108_);
lean_dec_ref(v_inst_107_);
lean_dec(v_inst_106_);
lean_dec_ref(v_inst_105_);
lean_dec_ref(v_inst_104_);
return v_res_111_;
}
}
static lean_object* _init_lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_113_ = lp_mathlib_Complex_ofReal(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0(lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___closed__0, &lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___closed__0);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0___boxed(lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___lam__0(v_x_116_);
lean_dec_ref(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg(){
_start:
{
lean_object* v___f_120_; 
v___f_120_ = ((lean_object*)(lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___closed__0));
return v___f_120_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___boxed(lean_object* v___dummy_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg();
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1(lean_object* v_E_123_, lean_object* v_n_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_s_129_, lean_object* v_V_130_, lean_object* v_e_131_){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = ((lean_object*)(lp_GRH_New_Space_instAddCommGroupForm___aux__1___redArg___closed__0));
return v___f_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__1___boxed(lean_object* v_E_133_, lean_object* v_n_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_s_139_, lean_object* v_V_140_, lean_object* v_e_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_GRH_New_Space_instAddCommGroupForm___aux__1(v_E_133_, v_n_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_s_139_, v_V_140_, v_e_141_);
lean_dec_ref(v_e_141_);
lean_dec_ref(v_V_140_);
lean_dec_ref(v_s_139_);
lean_dec_ref(v_inst_138_);
lean_dec(v_inst_137_);
lean_dec_ref(v_inst_136_);
lean_dec_ref(v_inst_135_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3___redArg___lam__0(lean_object* v_a_143_, lean_object* v_b_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_146_; lean_object* v_re_147_; lean_object* v_im_148_; lean_object* v___x_149_; lean_object* v_re_150_; lean_object* v_im_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_160_; 
lean_inc_ref(v___y_145_);
v___x_146_ = lean_apply_1(v_a_143_, v___y_145_);
v_re_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_re_147_);
v_im_148_ = lean_ctor_get(v___x_146_, 1);
lean_inc(v_im_148_);
lean_dec_ref(v___x_146_);
v___x_149_ = lean_apply_1(v_b_144_, v___y_145_);
v_re_150_ = lean_ctor_get(v___x_149_, 0);
v_im_151_ = lean_ctor_get(v___x_149_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_160_ == 0)
{
v___x_153_ = v___x_149_;
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_im_151_);
lean_inc(v_re_150_);
lean_dec(v___x_149_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___x_158_; 
v___f_155_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_155_, 0, v_re_147_);
lean_closure_set(v___f_155_, 1, v_re_150_);
v___f_156_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_156_, 0, v_im_148_);
lean_closure_set(v___f_156_, 1, v_im_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___f_156_);
lean_ctor_set(v___x_153_, 0, v___f_155_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___f_155_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___f_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3___redArg(lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_163_, 0, v_a_161_);
lean_closure_set(v___f_163_, 1, v_b_162_);
return v___f_163_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3(lean_object* v_E_164_, lean_object* v_n_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_s_170_, lean_object* v_V_171_, lean_object* v_e_172_, lean_object* v_a_173_, lean_object* v_b_174_){
_start:
{
lean_object* v___f_175_; 
v___f_175_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_175_, 0, v_a_173_);
lean_closure_set(v___f_175_, 1, v_b_174_);
return v___f_175_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__3___boxed(lean_object* v_E_176_, lean_object* v_n_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_s_182_, lean_object* v_V_183_, lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = lp_GRH_New_Space_instAddCommGroupForm___aux__3(v_E_176_, v_n_177_, v_inst_178_, v_inst_179_, v_inst_180_, v_inst_181_, v_s_182_, v_V_183_, v_e_184_, v_a_185_, v_b_186_);
lean_dec_ref(v_e_184_);
lean_dec_ref(v_V_183_);
lean_dec_ref(v_s_182_);
lean_dec_ref(v_inst_181_);
lean_dec(v_inst_180_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8___redArg___lam__0(lean_object* v_x_188_, lean_object* v_n_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_191_; lean_object* v_toNSMul_192_; lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_191_ = lp_mathlib_Real_instAddMonoid;
v_toNSMul_192_ = lean_ctor_get(v___x_191_, 2);
v___x_193_ = lean_apply_1(v_x_188_, v___y_190_);
lean_inc(v_toNSMul_192_);
v___f_194_ = lean_alloc_closure((void*)(lp_mathlib_NSMul_toSMul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_194_, 0, v_toNSMul_192_);
v___x_195_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_196_ = lp_mathlib_Complex_mulAux___redArg(v___f_194_, v_n_189_, v___x_195_, v___x_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8___redArg(lean_object* v_n_197_, lean_object* v_x_198_){
_start:
{
lean_object* v___f_199_; 
v___f_199_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__8___redArg___lam__0), 3, 2);
lean_closure_set(v___f_199_, 0, v_x_198_);
lean_closure_set(v___f_199_, 1, v_n_197_);
return v___f_199_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8(lean_object* v_E_200_, lean_object* v_n_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_s_206_, lean_object* v_V_207_, lean_object* v_e_208_, lean_object* v_n_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__8___redArg___lam__0), 3, 2);
lean_closure_set(v___f_211_, 0, v_x_210_);
lean_closure_set(v___f_211_, 1, v_n_209_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__8___boxed(lean_object* v_E_212_, lean_object* v_n_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_s_218_, lean_object* v_V_219_, lean_object* v_e_220_, lean_object* v_n_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_GRH_New_Space_instAddCommGroupForm___aux__8(v_E_212_, v_n_213_, v_inst_214_, v_inst_215_, v_inst_216_, v_inst_217_, v_s_218_, v_V_219_, v_e_220_, v_n_221_, v_x_222_);
lean_dec_ref(v_e_220_);
lean_dec_ref(v_V_219_);
lean_dec_ref(v_s_218_);
lean_dec_ref(v_inst_217_);
lean_dec(v_inst_216_);
lean_dec_ref(v_inst_215_);
lean_dec_ref(v_inst_214_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12___redArg___lam__0(lean_object* v_a_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_226_; lean_object* v_re_227_; lean_object* v_im_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
v___x_226_ = lean_apply_1(v_a_224_, v___y_225_);
v_re_227_ = lean_ctor_get(v___x_226_, 0);
v_im_228_ = lean_ctor_get(v___x_226_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_237_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_im_228_);
lean_inc(v_re_227_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___x_235_; 
v___f_232_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_232_, 0, v_re_227_);
v___f_233_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_233_, 0, v_im_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___f_233_);
lean_ctor_set(v___x_230_, 0, v___f_232_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___f_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12___redArg(lean_object* v_a_238_){
_start:
{
lean_object* v___f_239_; 
v___f_239_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__12___redArg___lam__0), 2, 1);
lean_closure_set(v___f_239_, 0, v_a_238_);
return v___f_239_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12(lean_object* v_E_240_, lean_object* v_n_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_s_246_, lean_object* v_V_247_, lean_object* v_e_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__12___redArg___lam__0), 2, 1);
lean_closure_set(v___f_250_, 0, v_a_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__12___boxed(lean_object* v_E_251_, lean_object* v_n_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_s_257_, lean_object* v_V_258_, lean_object* v_e_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = lp_GRH_New_Space_instAddCommGroupForm___aux__12(v_E_251_, v_n_252_, v_inst_253_, v_inst_254_, v_inst_255_, v_inst_256_, v_s_257_, v_V_258_, v_e_259_, v_a_260_);
lean_dec_ref(v_e_259_);
lean_dec_ref(v_V_258_);
lean_dec_ref(v_s_257_);
lean_dec_ref(v_inst_256_);
lean_dec(v_inst_255_);
lean_dec_ref(v_inst_254_);
lean_dec_ref(v_inst_253_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14___redArg___lam__0(lean_object* v_a_262_, lean_object* v_b_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_265_; lean_object* v_re_266_; lean_object* v_im_267_; lean_object* v___x_268_; lean_object* v_re_269_; lean_object* v_im_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_281_; 
lean_inc_ref(v___y_264_);
v___x_265_ = lean_apply_1(v_a_262_, v___y_264_);
v_re_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_re_266_);
v_im_267_ = lean_ctor_get(v___x_265_, 1);
lean_inc(v_im_267_);
lean_dec_ref(v___x_265_);
v___x_268_ = lean_apply_1(v_b_263_, v___y_264_);
v_re_269_ = lean_ctor_get(v___x_268_, 0);
v_im_270_ = lean_ctor_get(v___x_268_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_281_ == 0)
{
v___x_272_ = v___x_268_;
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_im_270_);
lean_inc(v_re_269_);
lean_dec(v___x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___x_279_; 
v___f_274_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_274_, 0, v_re_269_);
v___f_275_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_275_, 0, v_re_266_);
lean_closure_set(v___f_275_, 1, v___f_274_);
v___f_276_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_276_, 0, v_im_270_);
v___f_277_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_277_, 0, v_im_267_);
lean_closure_set(v___f_277_, 1, v___f_276_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___f_277_);
lean_ctor_set(v___x_272_, 0, v___f_275_);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___f_275_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___f_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14___redArg(lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v___f_284_; 
v___f_284_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__14___redArg___lam__0), 3, 2);
lean_closure_set(v___f_284_, 0, v_a_282_);
lean_closure_set(v___f_284_, 1, v_b_283_);
return v___f_284_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14(lean_object* v_E_285_, lean_object* v_n_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_s_291_, lean_object* v_V_292_, lean_object* v_e_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
lean_object* v___f_296_; 
v___f_296_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__14___redArg___lam__0), 3, 2);
lean_closure_set(v___f_296_, 0, v_a_294_);
lean_closure_set(v___f_296_, 1, v_b_295_);
return v___f_296_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__14___boxed(lean_object* v_E_297_, lean_object* v_n_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_s_303_, lean_object* v_V_304_, lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_GRH_New_Space_instAddCommGroupForm___aux__14(v_E_297_, v_n_298_, v_inst_299_, v_inst_300_, v_inst_301_, v_inst_302_, v_s_303_, v_V_304_, v_e_305_, v_a_306_, v_b_307_);
lean_dec_ref(v_e_305_);
lean_dec_ref(v_V_304_);
lean_dec_ref(v_s_303_);
lean_dec_ref(v_inst_302_);
lean_dec(v_inst_301_);
lean_dec_ref(v_inst_300_);
lean_dec_ref(v_inst_299_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16___redArg___lam__0(lean_object* v_x_309_, lean_object* v_n_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_312_; lean_object* v_toZSMul_313_; lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_312_ = lp_mathlib_Real_instAddGroup;
v_toZSMul_313_ = lean_ctor_get(v___x_312_, 3);
v___x_314_ = lean_apply_1(v_x_309_, v___y_311_);
lean_inc(v_toZSMul_313_);
v___f_315_ = lean_alloc_closure((void*)(lp_mathlib_ZSMul_toSMul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_315_, 0, v_toZSMul_313_);
v___x_316_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_317_ = lp_mathlib_Complex_mulAux___redArg(v___f_315_, v_n_310_, v___x_316_, v___x_314_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16___redArg(lean_object* v_n_318_, lean_object* v_x_319_){
_start:
{
lean_object* v___f_320_; 
v___f_320_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__16___redArg___lam__0), 3, 2);
lean_closure_set(v___f_320_, 0, v_x_319_);
lean_closure_set(v___f_320_, 1, v_n_318_);
return v___f_320_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16(lean_object* v_E_321_, lean_object* v_n_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_s_327_, lean_object* v_V_328_, lean_object* v_e_329_, lean_object* v_n_330_, lean_object* v_x_331_){
_start:
{
lean_object* v___f_332_; 
v___f_332_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instAddCommGroupForm___aux__16___redArg___lam__0), 3, 2);
lean_closure_set(v___f_332_, 0, v_x_331_);
lean_closure_set(v___f_332_, 1, v_n_330_);
return v___f_332_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instAddCommGroupForm___aux__16___boxed(lean_object* v_E_333_, lean_object* v_n_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_s_339_, lean_object* v_V_340_, lean_object* v_e_341_, lean_object* v_n_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = lp_GRH_New_Space_instAddCommGroupForm___aux__16(v_E_333_, v_n_334_, v_inst_335_, v_inst_336_, v_inst_337_, v_inst_338_, v_s_339_, v_V_340_, v_e_341_, v_n_342_, v_x_343_);
lean_dec_ref(v_e_341_);
lean_dec_ref(v_V_340_);
lean_dec_ref(v_s_339_);
lean_dec_ref(v_inst_338_);
lean_dec(v_inst_337_);
lean_dec_ref(v_inst_336_);
lean_dec_ref(v_inst_335_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0(lean_object* v_c_348_, lean_object* v_x_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_re_351_; lean_object* v_im_352_; lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; 
v_re_351_ = lean_ctor_get(v_c_348_, 0);
lean_inc(v_re_351_);
v_im_352_ = lean_ctor_get(v_c_348_, 1);
lean_inc(v_im_352_);
lean_dec_ref(v_c_348_);
v___x_353_ = lean_apply_1(v_x_349_, v___y_350_);
v___f_354_ = ((lean_object*)(lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0___closed__1));
v___x_355_ = lp_mathlib_Complex_mulAux___redArg(v___f_354_, v_re_351_, v_im_352_, v___x_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg(lean_object* v_c_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___f_358_; 
v___f_358_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_358_, 0, v_c_356_);
lean_closure_set(v___f_358_, 1, v_x_357_);
return v___f_358_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1(lean_object* v_E_359_, lean_object* v_n_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_s_365_, lean_object* v_V_366_, lean_object* v_e_367_, lean_object* v_c_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___f_370_; 
v___f_370_ = lean_alloc_closure((void*)(lp_GRH_New_Space_instModuleComplexForm___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_370_, 0, v_c_368_);
lean_closure_set(v___f_370_, 1, v_x_369_);
return v___f_370_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instModuleComplexForm___aux__1___boxed(lean_object* v_E_371_, lean_object* v_n_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_s_377_, lean_object* v_V_378_, lean_object* v_e_379_, lean_object* v_c_380_, lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = lp_GRH_New_Space_instModuleComplexForm___aux__1(v_E_371_, v_n_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_s_377_, v_V_378_, v_e_379_, v_c_380_, v_x_381_);
lean_dec_ref(v_e_379_);
lean_dec_ref(v_V_378_);
lean_dec_ref(v_s_377_);
lean_dec_ref(v_inst_376_);
lean_dec(v_inst_375_);
lean_dec_ref(v_inst_374_);
lean_dec_ref(v_inst_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___lam__0(lean_object* v_x_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_apply_1(v_x_383_, v___y_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg(){
_start:
{
lean_object* v___f_388_; 
v___f_388_ = ((lean_object*)(lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___closed__0));
return v___f_388_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___boxed(lean_object* v___dummy_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex(lean_object* v_E_391_, lean_object* v_n_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_s_397_, lean_object* v_V_398_, lean_object* v_e_399_){
_start:
{
lean_object* v___f_400_; 
v___f_400_ = ((lean_object*)(lp_GRH_New_Space_instCoeFunFormForallGComplex___redArg___closed__0));
return v___f_400_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_instCoeFunFormForallGComplex___boxed(lean_object* v_E_401_, lean_object* v_n_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_s_407_, lean_object* v_V_408_, lean_object* v_e_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = lp_GRH_New_Space_instCoeFunFormForallGComplex(v_E_401_, v_n_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_inst_406_, v_s_407_, v_V_408_, v_e_409_);
lean_dec_ref(v_e_409_);
lean_dec_ref(v_V_408_);
lean_dec_ref(v_s_407_);
lean_dec_ref(v_inst_406_);
lean_dec(v_inst_405_);
lean_dec_ref(v_inst_404_);
lean_dec_ref(v_inst_403_);
return v_res_410_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Reduction_DefiniteClassSums(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_Basic(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Reduction_DefiniteClassSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1 = _init_lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1();
lean_mark_persistent(lp_GRH_New_Space_IsAutomorphic_map_u2082___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
