// Lean compiler output
// Module: Lib.General.Measure.IdempotentKernel
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Mathlib"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__10_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__11_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunProp"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__12 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__12_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funPropTacStx"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__13 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__13_value;
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(118, 213, 161, 2, 73, 184, 31, 228)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value_aux_0),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(210, 10, 180, 159, 248, 97, 218, 144)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value_aux_1),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 118, 4, 116, 28, 199, 219)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value_aux_2),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(146, 162, 46, 139, 110, 137, 217, 136)}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14_value;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fun_prop"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__15_value;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__16;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__17;
static const lean_string_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__18 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__18_value;
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value_aux_0),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value_aux_1),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value_aux_2),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19_value;
static const lean_ctor_object lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__20 = (const lean_object*)&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__20_value;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__26;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__27;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__28;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32;
LEAN_EXPORT lean_object* lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_IsBoundedMeasurable_integrable__mul__comp___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integrable__integral__skew__product___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integral__integral__skew__product___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integral__skew__product___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integrable__mul__smul__comp__mul___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integral__smul__integral__swap___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integral__smul__integral__eq__integral__conv__smul___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_integral__conv___auto__1;
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__16(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__15));
v___x_32_ = l_Lean_mkAtom(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__17(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__16, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__16_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__16);
v___x_34_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5));
v___x_35_ = lean_array_push(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__21(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__20));
v___x_47_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5));
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__22(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__21, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__21_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__21);
v___x_50_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__19));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__23(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__22, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__22_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__22);
v___x_54_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__17, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__17_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__17);
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__24(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__20));
v___x_57_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__23, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__23_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__23);
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__25(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__20));
v___x_60_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__24, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__24_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__24);
v___x_61_ = lean_array_push(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__26(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__25, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__25_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__25);
v___x_63_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__14));
v___x_64_ = lean_box(2);
v___x_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__27(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__26, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__26_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__26);
v___x_67_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5));
v___x_68_ = lean_array_push(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__28(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__27, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__27_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__27);
v___x_70_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__9));
v___x_71_ = lean_box(2);
v___x_72_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__29(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__28, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__28_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__28);
v___x_74_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5));
v___x_75_ = lean_array_push(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__30(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__29, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__29_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__29);
v___x_77_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__7));
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__31(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__30, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__30_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__30);
v___x_81_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__5));
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__31, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__31_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__31);
v___x_84_ = ((lean_object*)(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__4));
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_87_;
}
}
static lean_object* _init_lp_GRH_New_IsBoundedMeasurable_integrable__mul__comp___auto__1(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_88_;
}
}
static lean_object* _init_lp_GRH_New_integrable__integral__skew__product___auto__1(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_89_;
}
}
static lean_object* _init_lp_GRH_New_integral__integral__skew__product___auto__1(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_New_integral__skew__product___auto__1(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_91_;
}
}
static lean_object* _init_lp_GRH_New_integrable__mul__smul__comp__mul___auto__1(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_92_;
}
}
static lean_object* _init_lp_GRH_New_integral__smul__integral__swap___auto__1(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_93_;
}
}
static lean_object* _init_lp_GRH_New_integral__smul__integral__eq__integral__conv__smul___auto__1(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_94_;
}
}
static lean_object* _init_lp_GRH_New_integral__conv___auto__1(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32, &lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32_once, _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1___closed__32);
return v___x_95_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Measure_IdempotentKernel(uint8_t builtin) {
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
lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1 = _init_lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1();
lean_mark_persistent(lp_GRH_New_IsBoundedMeasurable_of__continuous___auto__1);
lp_GRH_New_IsBoundedMeasurable_integrable__mul__comp___auto__1 = _init_lp_GRH_New_IsBoundedMeasurable_integrable__mul__comp___auto__1();
lean_mark_persistent(lp_GRH_New_IsBoundedMeasurable_integrable__mul__comp___auto__1);
lp_GRH_New_integrable__integral__skew__product___auto__1 = _init_lp_GRH_New_integrable__integral__skew__product___auto__1();
lean_mark_persistent(lp_GRH_New_integrable__integral__skew__product___auto__1);
lp_GRH_New_integral__integral__skew__product___auto__1 = _init_lp_GRH_New_integral__integral__skew__product___auto__1();
lean_mark_persistent(lp_GRH_New_integral__integral__skew__product___auto__1);
lp_GRH_New_integral__skew__product___auto__1 = _init_lp_GRH_New_integral__skew__product___auto__1();
lean_mark_persistent(lp_GRH_New_integral__skew__product___auto__1);
lp_GRH_New_integrable__mul__smul__comp__mul___auto__1 = _init_lp_GRH_New_integrable__mul__smul__comp__mul___auto__1();
lean_mark_persistent(lp_GRH_New_integrable__mul__smul__comp__mul___auto__1);
lp_GRH_New_integral__smul__integral__swap___auto__1 = _init_lp_GRH_New_integral__smul__integral__swap___auto__1();
lean_mark_persistent(lp_GRH_New_integral__smul__integral__swap___auto__1);
lp_GRH_New_integral__smul__integral__eq__integral__conv__smul___auto__1 = _init_lp_GRH_New_integral__smul__integral__eq__integral__conv__smul___auto__1();
lean_mark_persistent(lp_GRH_New_integral__smul__integral__eq__integral__conv__smul___auto__1);
lp_GRH_New_integral__conv___auto__1 = _init_lp_GRH_New_integral__conv___auto__1();
lean_mark_persistent(lp_GRH_New_integral__conv___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
