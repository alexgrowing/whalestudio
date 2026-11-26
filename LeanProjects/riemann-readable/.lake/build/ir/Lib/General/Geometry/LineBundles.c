// Lean compiler output
// Module: Lib.General.Geometry.LineBundles
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Quotient_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Quotient_map_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddGroup_ofRightAxioms___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__0 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__1 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__2 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__3 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__3_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__4 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__4_value;
static const lean_array_object lp_GRH_New_LineBundle_cover___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__5 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__5_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__6 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__6_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__7 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__7_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__8 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__8_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__9 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__9_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__10 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__10_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__11 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__11_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__12;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__13;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__14 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__14_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__15_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__15_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__15_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__15 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__15_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__9_value),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__5_value)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__16 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__16_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__17;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__18;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__19;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__20;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__21;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__22 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__22_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__23;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__24;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__25 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__25_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__26_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__26_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__26_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__25_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__26 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__26_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__27 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__27_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__28;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__29;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__30;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__31;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "iSup_inf_iSup"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__32 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__32_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__33;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__34;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__32_value),LEAN_SCALAR_PTR_LITERAL(43, 19, 46, 160, 139, 248, 202, 251)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__35 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__35_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__36;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__37;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__38;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__39;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__40 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__40_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__41;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__42;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "iInf_iSup_eq_of_finite"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__43 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__43_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__44;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__45;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__43_value),LEAN_SCALAR_PTR_LITERAL(153, 104, 245, 59, 191, 23, 214, 238)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__46 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__46_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__47;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__48;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__49;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__50;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__51;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__52;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LineBundle.cover"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__53 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__53_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__54;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__55;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LineBundle"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__56 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__56_value;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cover"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__57 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__57_value;
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__56_value),LEAN_SCALAR_PTR_LITERAL(202, 245, 39, 242, 162, 42, 4, 76)}};
static const lean_ctor_object lp_GRH_New_LineBundle_cover___autoParam___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__58_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__57_value),LEAN_SCALAR_PTR_LITERAL(101, 227, 140, 21, 230, 98, 82, 121)}};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__58 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__58_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__59;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__60;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__61;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__62;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__63;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__64;
static const lean_string_object lp_GRH_New_LineBundle_cover___autoParam___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__65 = (const lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__65_value;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__66;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__67;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__68;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__69;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__70;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__71;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__72;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__73;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__74;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__75;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__76;
static lean_once_cell_t lp_GRH_New_LineBundle_cover___autoParam___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_cover___autoParam___closed__77;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_cover___autoParam;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__0 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__0_value;
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__1_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__1_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__1_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__1 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__1_value;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__2 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__2_value;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__3;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__4;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__5;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__6;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__7;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "PointFn.IsRegularOn"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__8 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__8_value;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__9;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__10;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "PointFn"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__11 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__11_value;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "IsRegularOn"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__12 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__12_value;
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__11_value),LEAN_SCALAR_PTR_LITERAL(156, 250, 121, 151, 2, 87, 89, 116)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__13_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__12_value),LEAN_SCALAR_PTR_LITERAL(111, 237, 89, 210, 87, 150, 234, 23)}};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__13 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__13_value;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__14;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__15;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__16;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__17;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__18;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__19 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__19_value;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__20 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__20_value;
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__21_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__21_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__19_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__21_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__20_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__21 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__21_value;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LineBundle.regular"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__22 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__22_value;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__23;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__24;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__25 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__25_value;
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__56_value),LEAN_SCALAR_PTR_LITERAL(202, 245, 39, 242, 162, 42, 4, 76)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__26_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__25_value),LEAN_SCALAR_PTR_LITERAL(150, 140, 117, 8, 234, 62, 27, 156)}};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__26 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__26_value;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__27;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__28;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__29 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__29_value;
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__30_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__30_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__19_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_GRH_New_LineBundle_regular___autoParam___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__30_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__29_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__30 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__30_value;
static const lean_string_object lp_GRH_New_LineBundle_regular___autoParam___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__31 = (const lean_object*)&lp_GRH_New_LineBundle_regular___autoParam___closed__31_value;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__32;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__33;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__34;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__35;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__36;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__37;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__38;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__39;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__40;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__41;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__42;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__43;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__44;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__45;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__46;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__47;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__48;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__49;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__50;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__51;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__52;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__53;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__54;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__55;
static lean_once_cell_t lp_GRH_New_LineBundle_regular___autoParam___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_regular___autoParam___closed__56;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_regular___autoParam;
static const lean_string_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__0 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__0_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__1 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__1_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__2 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__2_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__3 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__3_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__4 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__4_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__5;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__6;
static const lean_string_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "contextual"};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__7 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__7_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__8;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__9;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__7_value),LEAN_SCALAR_PTR_LITERAL(229, 190, 84, 18, 151, 13, 33, 25)}};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__10 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__10_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__11;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__12;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__13;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__14;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__15;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__16;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__17;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__18;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__19;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__20;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__21;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__22;
static const lean_string_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "LineBundle.transition_self"};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__23 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__23_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__24;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__25;
static const lean_string_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "transition_self"};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__26 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__26_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__56_value),LEAN_SCALAR_PTR_LITERAL(202, 245, 39, 242, 162, 42, 4, 76)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__self___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__27_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__26_value),LEAN_SCALAR_PTR_LITERAL(113, 2, 77, 178, 247, 173, 51, 76)}};
static const lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__27 = (const lean_object*)&lp_GRH_New_LineBundle_transition__self___autoParam___closed__27_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__28;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__29;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__30;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__31;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__32;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__33;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__34;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__35;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__36;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__37;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__38;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__39;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__40;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__41;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__42;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__43;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__self___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__self___autoParam___closed__44;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_transition__self___autoParam;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__0 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__0_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__2 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__2_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__4 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__4_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__5;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__6;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__7 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__7_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__7_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__9 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__9_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__10;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__11;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "LineBundle.transition_trans"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__12 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__12_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__13;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__14;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "transition_trans"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__15 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__15_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__56_value),LEAN_SCALAR_PTR_LITERAL(202, 245, 39, 242, 162, 42, 4, 76)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__16_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(57, 88, 196, 168, 136, 197, 119, 114)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__16 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__16_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__18;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__19;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__20;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__21;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Finset.prod_mul_distrib"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__22 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__22_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__23;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__24;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Finset"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__25 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__25_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "prod_mul_distrib"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__26 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__26_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__25_value),LEAN_SCALAR_PTR_LITERAL(87, 75, 221, 45, 221, 79, 84, 42)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__27_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__26_value),LEAN_SCALAR_PTR_LITERAL(81, 30, 183, 160, 37, 108, 242, 15)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__27 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__27_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__28;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__29;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__30;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__31;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__32;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__33;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__34;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__35;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__36;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__37;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__38;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__39;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__40;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__41;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__42;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__43;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__44;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__45;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__46;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__47;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__48;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__49;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__50;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__51;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__52;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__53;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__54 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__54_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__55;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__56;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__57;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__58;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__59 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__59_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__60;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__61;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__62 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__62_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__62_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__64;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__65;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__66;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__67;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__68 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__68_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__68_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69_value;
static const lean_string_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__70 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__70_value;
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value_aux_0),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value_aux_1),((lean_object*)&lp_GRH_New_LineBundle_cover___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value_aux_2),((lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__70_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71 = (const lean_object*)&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71_value;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__72;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__73;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__74;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__75;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__76;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__77;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__78;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__79;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__80;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__81;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__82;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__83;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__84;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__85;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__86;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__87;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__88;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__89;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__90;
static lean_once_cell_t lp_GRH_New_LineBundle_transition__trans___autoParam___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam___closed__91;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_transition__trans___autoParam;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___lam__1(lean_object*);
static const lean_closure_object lp_GRH_New_LineBundle_one___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_LineBundle_one___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_LineBundle_one___redArg___closed__0 = (const lean_object*)&lp_GRH_New_LineBundle_one___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_LineBundle_one___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_LineBundle_one___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_LineBundle_one___redArg___closed__1 = (const lean_object*)&lp_GRH_New_LineBundle_one___redArg___closed__1_value;
static const lean_ctor_object lp_GRH_New_LineBundle_one___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GRH_New_LineBundle_one___redArg___closed__1_value),((lean_object*)&lp_GRH_New_LineBundle_one___redArg___closed__0_value)}};
static const lean_object* lp_GRH_New_LineBundle_one___redArg___closed__2 = (const lean_object*)&lp_GRH_New_LineBundle_one___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_LineBundle_one___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_LineBundle_one___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_LineBundle_mul___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_LineBundle_mul___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_LineBundle_mul___redArg___closed__0 = (const lean_object*)&lp_GRH_New_LineBundle_mul___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_picClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_picClass(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_picClass___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_instAddPic___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_instAddPic___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_instAddPic___redArg___closed__0 = (const lean_object*)&lp_GRH_New_instAddPic___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_instAddPic___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Quotient_map_u2082, .m_arity = 10, .m_num_fixed = 8, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_instAddPic___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_instAddPic___redArg___closed__1 = (const lean_object*)&lp_GRH_New_instAddPic___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instAddPic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instAddPic___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___redArg___lam__0(lean_object*);
static const lean_closure_object lp_GRH_New_instNegPic___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_instNegPic___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_instNegPic___redArg___closed__0 = (const lean_object*)&lp_GRH_New_instNegPic___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_instNegPic___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Quotient_map, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_instNegPic___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_instNegPic___redArg___closed__1 = (const lean_object*)&lp_GRH_New_instNegPic___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instNegPic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instNegPic___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instZeroPic___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instZeroPic___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instZeroPic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instZeroPic___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instAddCommGroupPic___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instAddCommGroupPic___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instAddCommGroupPic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instAddCommGroupPic___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic___boxed(lean_object*);
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__12, &lp_GRH_New_LineBundle_cover___autoParam___closed__12_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__12);
v___x_30_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_43_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__17, &lp_GRH_New_LineBundle_cover___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__17);
v___x_46_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__18, &lp_GRH_New_LineBundle_cover___autoParam___closed__18_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__18);
v___x_50_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__13, &lp_GRH_New_LineBundle_cover___autoParam___closed__13_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_53_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__19, &lp_GRH_New_LineBundle_cover___autoParam___closed__19_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__19);
v___x_54_ = lean_array_push(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__21(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_56_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__20, &lp_GRH_New_LineBundle_cover___autoParam___closed__20_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__20);
v___x_57_ = lean_array_push(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__23(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__22));
v___x_60_ = l_Lean_mkAtom(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__24(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__23, &lp_GRH_New_LineBundle_cover___autoParam___closed__23_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__23);
v___x_62_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__28(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__27));
v___x_72_ = l_Lean_mkAtom(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__29(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__28, &lp_GRH_New_LineBundle_cover___autoParam___closed__28_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__28);
v___x_74_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_75_ = lean_array_push(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__30(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__29, &lp_GRH_New_LineBundle_cover___autoParam___closed__29_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__29);
v___x_77_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__31(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__30, &lp_GRH_New_LineBundle_cover___autoParam___closed__30_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__30);
v___x_81_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__17, &lp_GRH_New_LineBundle_cover___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__17);
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__33(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__32));
v___x_85_ = lean_string_utf8_byte_size(v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__34(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__33, &lp_GRH_New_LineBundle_cover___autoParam___closed__33_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__33);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__32));
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_86_);
return v___x_89_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__36(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = lean_box(0);
v___x_93_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__35));
v___x_94_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__34, &lp_GRH_New_LineBundle_cover___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__34);
v___x_95_ = lean_box(2);
v___x_96_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
lean_ctor_set(v___x_96_, 3, v___x_92_);
return v___x_96_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__37(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__36, &lp_GRH_New_LineBundle_cover___autoParam___closed__36_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__36);
v___x_98_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__31, &lp_GRH_New_LineBundle_cover___autoParam___closed__31_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__31);
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__38(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__37, &lp_GRH_New_LineBundle_cover___autoParam___closed__37_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__37);
v___x_101_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_102_ = lean_box(2);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__39(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__38, &lp_GRH_New_LineBundle_cover___autoParam___closed__38_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__38);
v___x_105_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_106_ = lean_array_push(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__41(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__40));
v___x_109_ = l_Lean_mkAtom(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__42(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__41, &lp_GRH_New_LineBundle_cover___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__41);
v___x_111_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__39, &lp_GRH_New_LineBundle_cover___autoParam___closed__39_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__39);
v___x_112_ = lean_array_push(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__44(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__43));
v___x_115_ = lean_string_utf8_byte_size(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__45(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__44, &lp_GRH_New_LineBundle_cover___autoParam___closed__44_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__44);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__43));
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__47(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = lean_box(0);
v___x_123_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__46));
v___x_124_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__45, &lp_GRH_New_LineBundle_cover___autoParam___closed__45_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__45);
v___x_125_ = lean_box(2);
v___x_126_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
lean_ctor_set(v___x_126_, 2, v___x_123_);
lean_ctor_set(v___x_126_, 3, v___x_122_);
return v___x_126_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__48(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__47, &lp_GRH_New_LineBundle_cover___autoParam___closed__47_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__47);
v___x_128_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__31, &lp_GRH_New_LineBundle_cover___autoParam___closed__31_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__31);
v___x_129_ = lean_array_push(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__49(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__48, &lp_GRH_New_LineBundle_cover___autoParam___closed__48_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__48);
v___x_131_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_132_ = lean_box(2);
v___x_133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
return v___x_133_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__50(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__49, &lp_GRH_New_LineBundle_cover___autoParam___closed__49_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__49);
v___x_135_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__42, &lp_GRH_New_LineBundle_cover___autoParam___closed__42_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__42);
v___x_136_ = lean_array_push(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__51(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__41, &lp_GRH_New_LineBundle_cover___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__41);
v___x_138_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__50, &lp_GRH_New_LineBundle_cover___autoParam___closed__50_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__50);
v___x_139_ = lean_array_push(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__52(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_141_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__17, &lp_GRH_New_LineBundle_cover___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__17);
v___x_142_ = lean_array_push(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__54(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__53));
v___x_145_ = lean_string_utf8_byte_size(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__55(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__54, &lp_GRH_New_LineBundle_cover___autoParam___closed__54_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__54);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__53));
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_146_);
return v___x_149_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__59(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_155_ = lean_box(0);
v___x_156_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__58));
v___x_157_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__55, &lp_GRH_New_LineBundle_cover___autoParam___closed__55_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__55);
v___x_158_ = lean_box(2);
v___x_159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
lean_ctor_set(v___x_159_, 3, v___x_155_);
return v___x_159_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__60(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__59, &lp_GRH_New_LineBundle_cover___autoParam___closed__59_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__59);
v___x_161_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__52, &lp_GRH_New_LineBundle_cover___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__52);
v___x_162_ = lean_array_push(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__61(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__60, &lp_GRH_New_LineBundle_cover___autoParam___closed__60_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__60);
v___x_164_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_165_ = lean_box(2);
v___x_166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
return v___x_166_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__62(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__61, &lp_GRH_New_LineBundle_cover___autoParam___closed__61_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__61);
v___x_168_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__51, &lp_GRH_New_LineBundle_cover___autoParam___closed__51_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__51);
v___x_169_ = lean_array_push(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__63(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__62, &lp_GRH_New_LineBundle_cover___autoParam___closed__62_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__62);
v___x_171_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_172_ = lean_box(2);
v___x_173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_170_);
return v___x_173_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__64(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__63, &lp_GRH_New_LineBundle_cover___autoParam___closed__63_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__63);
v___x_175_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__24, &lp_GRH_New_LineBundle_cover___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__24);
v___x_176_ = lean_array_push(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__66(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__65));
v___x_179_ = l_Lean_mkAtom(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__67(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__66, &lp_GRH_New_LineBundle_cover___autoParam___closed__66_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__66);
v___x_181_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__64, &lp_GRH_New_LineBundle_cover___autoParam___closed__64_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__64);
v___x_182_ = lean_array_push(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__68(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__67, &lp_GRH_New_LineBundle_cover___autoParam___closed__67_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__67);
v___x_184_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_185_ = lean_box(2);
v___x_186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_183_);
return v___x_186_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__69(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__68, &lp_GRH_New_LineBundle_cover___autoParam___closed__68_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__68);
v___x_188_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__21, &lp_GRH_New_LineBundle_cover___autoParam___closed__21_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__21);
v___x_189_ = lean_array_push(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__70(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_191_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__69, &lp_GRH_New_LineBundle_cover___autoParam___closed__69_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__69);
v___x_192_ = lean_array_push(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__71(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__70, &lp_GRH_New_LineBundle_cover___autoParam___closed__70_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__70);
v___x_194_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__11));
v___x_195_ = lean_box(2);
v___x_196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_193_);
return v___x_196_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__72(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__71, &lp_GRH_New_LineBundle_cover___autoParam___closed__71_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__71);
v___x_198_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_199_ = lean_array_push(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__73(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_200_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__72, &lp_GRH_New_LineBundle_cover___autoParam___closed__72_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__72);
v___x_201_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_202_ = lean_box(2);
v___x_203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_200_);
return v___x_203_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__74(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__73, &lp_GRH_New_LineBundle_cover___autoParam___closed__73_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__73);
v___x_205_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_206_ = lean_array_push(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__75(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__74, &lp_GRH_New_LineBundle_cover___autoParam___closed__74_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__74);
v___x_208_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__7));
v___x_209_ = lean_box(2);
v___x_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_207_);
return v___x_210_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__76(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__75, &lp_GRH_New_LineBundle_cover___autoParam___closed__75_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__75);
v___x_212_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_213_ = lean_array_push(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam___closed__77(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__76, &lp_GRH_New_LineBundle_cover___autoParam___closed__76_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__76);
v___x_215_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__4));
v___x_216_ = lean_box(2);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v___x_214_);
return v___x_217_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_cover___autoParam(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__77, &lp_GRH_New_LineBundle_cover___autoParam___closed__77_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__77);
return v___x_218_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__2));
v___x_227_ = l_Lean_mkAtom(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__4(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__3, &lp_GRH_New_LineBundle_regular___autoParam___closed__3_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__3);
v___x_229_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_230_ = lean_array_push(v___x_229_, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__5(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__18, &lp_GRH_New_LineBundle_cover___autoParam___closed__18_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__18);
v___x_232_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__4, &lp_GRH_New_LineBundle_regular___autoParam___closed__4_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__4);
v___x_233_ = lean_array_push(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__6(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_235_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__5, &lp_GRH_New_LineBundle_regular___autoParam___closed__5_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__5);
v___x_236_ = lean_array_push(v___x_235_, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__7(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_238_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__6, &lp_GRH_New_LineBundle_regular___autoParam___closed__6_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__6);
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__9(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__8));
v___x_242_ = lean_string_utf8_byte_size(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__10(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__9, &lp_GRH_New_LineBundle_regular___autoParam___closed__9_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__9);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__8));
v___x_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_243_);
return v___x_246_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__14(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__13));
v___x_254_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__10, &lp_GRH_New_LineBundle_regular___autoParam___closed__10_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__10);
v___x_255_ = lean_box(2);
v___x_256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_253_);
lean_ctor_set(v___x_256_, 3, v___x_252_);
return v___x_256_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__15(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__14, &lp_GRH_New_LineBundle_regular___autoParam___closed__14_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__14);
v___x_258_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__52, &lp_GRH_New_LineBundle_cover___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__52);
v___x_259_ = lean_array_push(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__16(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__15, &lp_GRH_New_LineBundle_regular___autoParam___closed__15_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__15);
v___x_261_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_262_ = lean_box(2);
v___x_263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_260_);
return v___x_263_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__17(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__16, &lp_GRH_New_LineBundle_regular___autoParam___closed__16_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__16);
v___x_265_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_266_ = lean_array_push(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__18(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__41, &lp_GRH_New_LineBundle_cover___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__41);
v___x_268_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__17, &lp_GRH_New_LineBundle_regular___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__17);
v___x_269_ = lean_array_push(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__23(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__22));
v___x_279_ = lean_string_utf8_byte_size(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__24(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__23, &lp_GRH_New_LineBundle_regular___autoParam___closed__23_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__23);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__22));
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
lean_ctor_set(v___x_283_, 2, v___x_280_);
return v___x_283_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__27(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_288_ = lean_box(0);
v___x_289_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__26));
v___x_290_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__24, &lp_GRH_New_LineBundle_regular___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__24);
v___x_291_ = lean_box(2);
v___x_292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
lean_ctor_set(v___x_292_, 3, v___x_288_);
return v___x_292_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__28(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__27, &lp_GRH_New_LineBundle_regular___autoParam___closed__27_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__27);
v___x_294_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_295_ = lean_array_push(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__32(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__31));
v___x_304_ = l_Lean_mkAtom(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__33(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__32, &lp_GRH_New_LineBundle_regular___autoParam___closed__32_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__32);
v___x_306_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__34(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__33, &lp_GRH_New_LineBundle_regular___autoParam___closed__33_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__33);
v___x_309_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__30));
v___x_310_ = lean_box(2);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_308_);
return v___x_311_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__35(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__34, &lp_GRH_New_LineBundle_regular___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__34);
v___x_313_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__36(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__34, &lp_GRH_New_LineBundle_regular___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__34);
v___x_316_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__35, &lp_GRH_New_LineBundle_regular___autoParam___closed__35_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__35);
v___x_317_ = lean_array_push(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__37(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__34, &lp_GRH_New_LineBundle_regular___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__34);
v___x_319_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__36, &lp_GRH_New_LineBundle_regular___autoParam___closed__36_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__36);
v___x_320_ = lean_array_push(v___x_319_, v___x_318_);
return v___x_320_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__38(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__34, &lp_GRH_New_LineBundle_regular___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__34);
v___x_322_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__37, &lp_GRH_New_LineBundle_regular___autoParam___closed__37_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__37);
v___x_323_ = lean_array_push(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__39(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__38, &lp_GRH_New_LineBundle_regular___autoParam___closed__38_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__38);
v___x_325_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_326_ = lean_box(2);
v___x_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v___x_324_);
return v___x_327_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__40(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__39, &lp_GRH_New_LineBundle_regular___autoParam___closed__39_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__39);
v___x_329_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__28, &lp_GRH_New_LineBundle_regular___autoParam___closed__28_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__28);
v___x_330_ = lean_array_push(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__41(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__40, &lp_GRH_New_LineBundle_regular___autoParam___closed__40_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__40);
v___x_332_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__21));
v___x_333_ = lean_box(2);
v___x_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
lean_ctor_set(v___x_334_, 2, v___x_331_);
return v___x_334_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__42(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__41, &lp_GRH_New_LineBundle_regular___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__41);
v___x_336_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__52, &lp_GRH_New_LineBundle_cover___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__52);
v___x_337_ = lean_array_push(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__43(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_338_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__42, &lp_GRH_New_LineBundle_regular___autoParam___closed__42_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__42);
v___x_339_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_340_ = lean_box(2);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v___x_338_);
return v___x_341_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__44(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__43, &lp_GRH_New_LineBundle_regular___autoParam___closed__43_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__43);
v___x_343_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__18, &lp_GRH_New_LineBundle_regular___autoParam___closed__18_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__18);
v___x_344_ = lean_array_push(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__45(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__44, &lp_GRH_New_LineBundle_regular___autoParam___closed__44_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__44);
v___x_346_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_347_ = lean_box(2);
v___x_348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
lean_ctor_set(v___x_348_, 2, v___x_345_);
return v___x_348_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__46(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__45, &lp_GRH_New_LineBundle_regular___autoParam___closed__45_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__45);
v___x_350_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__24, &lp_GRH_New_LineBundle_cover___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__24);
v___x_351_ = lean_array_push(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__47(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__66, &lp_GRH_New_LineBundle_cover___autoParam___closed__66_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__66);
v___x_353_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__46, &lp_GRH_New_LineBundle_regular___autoParam___closed__46_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__46);
v___x_354_ = lean_array_push(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__48(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__47, &lp_GRH_New_LineBundle_regular___autoParam___closed__47_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__47);
v___x_356_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_357_ = lean_box(2);
v___x_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
lean_ctor_set(v___x_358_, 2, v___x_355_);
return v___x_358_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__49(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__48, &lp_GRH_New_LineBundle_regular___autoParam___closed__48_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__48);
v___x_360_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__7, &lp_GRH_New_LineBundle_regular___autoParam___closed__7_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__7);
v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__50(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__49, &lp_GRH_New_LineBundle_regular___autoParam___closed__49_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__49);
v___x_363_ = ((lean_object*)(lp_GRH_New_LineBundle_regular___autoParam___closed__1));
v___x_364_ = lean_box(2);
v___x_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
return v___x_365_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__51(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__50, &lp_GRH_New_LineBundle_regular___autoParam___closed__50_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__50);
v___x_367_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__52(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__51, &lp_GRH_New_LineBundle_regular___autoParam___closed__51_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__51);
v___x_370_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_371_ = lean_box(2);
v___x_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
return v___x_372_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__53(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__52, &lp_GRH_New_LineBundle_regular___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__52);
v___x_374_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__54(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__53, &lp_GRH_New_LineBundle_regular___autoParam___closed__53_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__53);
v___x_377_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__7));
v___x_378_ = lean_box(2);
v___x_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_376_);
return v___x_379_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__55(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__54, &lp_GRH_New_LineBundle_regular___autoParam___closed__54_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__54);
v___x_381_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam___closed__56(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__55, &lp_GRH_New_LineBundle_regular___autoParam___closed__55_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__55);
v___x_384_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__4));
v___x_385_ = lean_box(2);
v___x_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
lean_ctor_set(v___x_386_, 2, v___x_383_);
return v___x_386_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_regular___autoParam(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&lp_GRH_New_LineBundle_regular___autoParam___closed__56, &lp_GRH_New_LineBundle_regular___autoParam___closed__56_once, _init_lp_GRH_New_LineBundle_regular___autoParam___closed__56);
return v___x_387_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__5(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__4));
v___x_402_ = l_Lean_mkAtom(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__6(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__5, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__5_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__5);
v___x_404_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_405_ = lean_array_push(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__8(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__7));
v___x_408_ = lean_string_utf8_byte_size(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__9(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__8, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__8_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__8);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__7));
v___x_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__11(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_415_ = lean_box(0);
v___x_416_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__10));
v___x_417_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__9, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__9_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__9);
v___x_418_ = lean_box(2);
v___x_419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_417_);
lean_ctor_set(v___x_419_, 2, v___x_416_);
lean_ctor_set(v___x_419_, 3, v___x_415_);
return v___x_419_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__12(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__11, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__11_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__11);
v___x_421_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__6, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__6_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__6);
v___x_422_ = lean_array_push(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__13(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__12, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__12_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__12);
v___x_424_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__3));
v___x_425_ = lean_box(2);
v___x_426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
lean_ctor_set(v___x_426_, 2, v___x_423_);
return v___x_426_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__14(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__13, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__13_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__13);
v___x_428_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_429_ = lean_array_push(v___x_428_, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__15(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_430_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__14, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__14_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__14);
v___x_431_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__1));
v___x_432_ = lean_box(2);
v___x_433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
lean_ctor_set(v___x_433_, 2, v___x_430_);
return v___x_433_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__16(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__15, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__15_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__15);
v___x_435_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_436_ = lean_array_push(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__17(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_437_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__16, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__16_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__16);
v___x_438_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_439_ = lean_box(2);
v___x_440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_437_);
return v___x_440_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__18(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__17, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__17);
v___x_442_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_443_ = lean_array_push(v___x_442_, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__19(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_444_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__18, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__18_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__18);
v___x_445_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__15));
v___x_446_ = lean_box(2);
v___x_447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_444_);
return v___x_447_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__20(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__19, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__19_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__19);
v___x_449_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__13, &lp_GRH_New_LineBundle_cover___autoParam___closed__13_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__13);
v___x_450_ = lean_array_push(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__21(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_452_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__20, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__20_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__20);
v___x_453_ = lean_array_push(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__22(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_455_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__21, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__21_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__21);
v___x_456_ = lean_array_push(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__24(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__23));
v___x_459_ = lean_string_utf8_byte_size(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__25(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__24, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__24);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__23));
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_460_);
return v___x_463_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__28(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_468_ = lean_box(0);
v___x_469_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__self___autoParam___closed__27));
v___x_470_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__25, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__25_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__25);
v___x_471_ = lean_box(2);
v___x_472_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_469_);
lean_ctor_set(v___x_472_, 3, v___x_468_);
return v___x_472_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__29(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__28, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__28_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__28);
v___x_474_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__52, &lp_GRH_New_LineBundle_cover___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__52);
v___x_475_ = lean_array_push(v___x_474_, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__30(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__29, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__29_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__29);
v___x_477_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_478_ = lean_box(2);
v___x_479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_477_);
lean_ctor_set(v___x_479_, 2, v___x_476_);
return v___x_479_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__31(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__30, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__30_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__30);
v___x_481_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_482_ = lean_array_push(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__32(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__31, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__31_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__31);
v___x_484_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_485_ = lean_box(2);
v___x_486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
return v___x_486_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__33(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__32, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__32_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__32);
v___x_488_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__24, &lp_GRH_New_LineBundle_cover___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__24);
v___x_489_ = lean_array_push(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__34(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__66, &lp_GRH_New_LineBundle_cover___autoParam___closed__66_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__66);
v___x_491_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__33, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__33_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__33);
v___x_492_ = lean_array_push(v___x_491_, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__35(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__34, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__34);
v___x_494_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_495_ = lean_box(2);
v___x_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_493_);
return v___x_496_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__36(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__35, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__35_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__35);
v___x_498_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__22, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__22_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__22);
v___x_499_ = lean_array_push(v___x_498_, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__37(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_501_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__36, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__36_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__36);
v___x_502_ = lean_array_push(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__38(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__37, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__37_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__37);
v___x_504_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__11));
v___x_505_ = lean_box(2);
v___x_506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_503_);
return v___x_506_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__39(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__38, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__38_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__38);
v___x_508_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_509_ = lean_array_push(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__40(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__39, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__39_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__39);
v___x_511_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_512_ = lean_box(2);
v___x_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
lean_ctor_set(v___x_513_, 2, v___x_510_);
return v___x_513_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__41(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__40, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__40_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__40);
v___x_515_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_516_ = lean_array_push(v___x_515_, v___x_514_);
return v___x_516_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__42(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__41, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__41);
v___x_518_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__7));
v___x_519_ = lean_box(2);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_517_);
return v___x_520_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__43(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__42, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__42_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__42);
v___x_522_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_523_ = lean_array_push(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__44(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__43, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__43_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__43);
v___x_525_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__4));
v___x_526_ = lean_box(2);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
lean_ctor_set(v___x_527_, 2, v___x_524_);
return v___x_527_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__self___autoParam(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__44, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__44_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__44);
return v___x_528_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__5(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__4));
v___x_543_ = l_Lean_mkAtom(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__6(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__5, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__5_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__5);
v___x_545_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_546_ = lean_array_push(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__10(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__9));
v___x_555_ = l_Lean_mkAtom(v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__11(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__10, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__10_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__10);
v___x_557_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_558_ = lean_array_push(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__13(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__12));
v___x_561_ = lean_string_utf8_byte_size(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__14(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__13, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__13_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__13);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__12));
v___x_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_563_);
lean_ctor_set(v___x_565_, 2, v___x_562_);
return v___x_565_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_570_ = lean_box(0);
v___x_571_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__16));
v___x_572_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__14, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__14_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__14);
v___x_573_ = lean_box(2);
v___x_574_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
lean_ctor_set(v___x_574_, 3, v___x_570_);
return v___x_574_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__18(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17);
v___x_576_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__52, &lp_GRH_New_LineBundle_cover___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__52);
v___x_577_ = lean_array_push(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__19(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__18, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__18_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__18);
v___x_579_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_580_ = lean_box(2);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_578_);
return v___x_581_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__20(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__19, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__19_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__19);
v___x_583_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__21(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__41, &lp_GRH_New_LineBundle_cover___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__41);
v___x_586_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__20, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__20_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__20);
v___x_587_ = lean_array_push(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__23(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__22));
v___x_590_ = lean_string_utf8_byte_size(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__24(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__23, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__23_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__23);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__22));
v___x_594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
return v___x_594_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__28(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_600_ = lean_box(0);
v___x_601_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__27));
v___x_602_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__24, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__24);
v___x_603_ = lean_box(2);
v___x_604_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_601_);
lean_ctor_set(v___x_604_, 3, v___x_600_);
return v___x_604_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__29(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__28, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__28_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__28);
v___x_606_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__31, &lp_GRH_New_LineBundle_cover___autoParam___closed__31_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__31);
v___x_607_ = lean_array_push(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__30(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__29, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__29_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__29);
v___x_609_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__26));
v___x_610_ = lean_box(2);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_608_);
return v___x_611_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__31(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__30, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__30_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__30);
v___x_613_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__21, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__21_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__21);
v___x_614_ = lean_array_push(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__32(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__31, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__31_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__31);
v___x_616_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_617_ = lean_box(2);
v___x_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
lean_ctor_set(v___x_618_, 2, v___x_615_);
return v___x_618_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__33(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__32, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__32_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__32);
v___x_620_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__24, &lp_GRH_New_LineBundle_cover___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__24);
v___x_621_ = lean_array_push(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__34(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__66, &lp_GRH_New_LineBundle_cover___autoParam___closed__66_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__66);
v___x_623_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__33, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__33_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__33);
v___x_624_ = lean_array_push(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__35(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__34, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__34_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__34);
v___x_626_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_627_ = lean_box(2);
v___x_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
return v___x_628_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__36(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__35, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__35_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__35);
v___x_630_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__self___autoParam___closed__22, &lp_GRH_New_LineBundle_transition__self___autoParam___closed__22_once, _init_lp_GRH_New_LineBundle_transition__self___autoParam___closed__22);
v___x_631_ = lean_array_push(v___x_630_, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__37(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_633_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__36, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__36_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__36);
v___x_634_ = lean_array_push(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__38(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__37, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__37_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__37);
v___x_636_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__11));
v___x_637_ = lean_box(2);
v___x_638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
lean_ctor_set(v___x_638_, 2, v___x_635_);
return v___x_638_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__39(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__38, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__38_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__38);
v___x_640_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_641_ = lean_array_push(v___x_640_, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__40(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__39, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__39_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__39);
v___x_643_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_644_ = lean_box(2);
v___x_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_642_);
return v___x_645_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__41(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__40, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__40_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__40);
v___x_647_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_648_ = lean_array_push(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__42(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__41, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__41_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__41);
v___x_650_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__7));
v___x_651_ = lean_box(2);
v___x_652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
lean_ctor_set(v___x_652_, 2, v___x_649_);
return v___x_652_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__43(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__42, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__42_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__42);
v___x_654_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_655_ = lean_array_push(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__44(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__43, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__43_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__43);
v___x_657_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__4));
v___x_658_ = lean_box(2);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_656_);
return v___x_659_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__45(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__44, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__44_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__44);
v___x_661_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__11, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__11_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__11);
v___x_662_ = lean_array_push(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__46(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__45, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__45_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__45);
v___x_664_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__8));
v___x_665_ = lean_box(2);
v___x_666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
lean_ctor_set(v___x_666_, 2, v___x_663_);
return v___x_666_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__47(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__46, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__46_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__46);
v___x_668_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_669_ = lean_array_push(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__48(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__47, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__47_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__47);
v___x_671_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_672_ = lean_box(2);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_670_);
return v___x_673_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__49(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__48, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__48_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__48);
v___x_675_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_676_ = lean_array_push(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__50(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__49, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__49_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__49);
v___x_678_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__7));
v___x_679_ = lean_box(2);
v___x_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
return v___x_680_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__51(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__50, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__50_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__50);
v___x_682_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_683_ = lean_array_push(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__52(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__51, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__51_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__51);
v___x_685_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__4));
v___x_686_ = lean_box(2);
v___x_687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
lean_ctor_set(v___x_687_, 2, v___x_684_);
return v___x_687_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__53(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__52, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__52_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__52);
v___x_689_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__6, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__6_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__6);
v___x_690_ = lean_array_push(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__55(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__54));
v___x_693_ = l_Lean_mkAtom(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__56(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__55, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__55_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__55);
v___x_695_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__53, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__53_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__53);
v___x_696_ = lean_array_push(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__57(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__56, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__56_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__56);
v___x_698_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__3));
v___x_699_ = lean_box(2);
v___x_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
lean_ctor_set(v___x_700_, 2, v___x_697_);
return v___x_700_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__58(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__57, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__57_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__57);
v___x_702_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_703_ = lean_array_push(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__60(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__59));
v___x_706_ = l_Lean_mkAtom(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__61(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__60, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__60_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__60);
v___x_708_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__58, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__58_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__58);
v___x_709_ = lean_array_push(v___x_708_, v___x_707_);
return v___x_709_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__64(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__62));
v___x_717_ = l_Lean_mkAtom(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__65(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__64, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__64_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__64);
v___x_719_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_720_ = lean_array_push(v___x_719_, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__66(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__18, &lp_GRH_New_LineBundle_cover___autoParam___closed__18_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__18);
v___x_722_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__65, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__65_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__65);
v___x_723_ = lean_array_push(v___x_722_, v___x_721_);
return v___x_723_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__67(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_725_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__66, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__66_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__66);
v___x_726_ = lean_array_push(v___x_725_, v___x_724_);
return v___x_726_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__72(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__17);
v___x_740_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__17, &lp_GRH_New_LineBundle_cover___autoParam___closed__17_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__17);
v___x_741_ = lean_array_push(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__73(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_742_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__72, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__72_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__72);
v___x_743_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__71));
v___x_744_ = lean_box(2);
v___x_745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
lean_ctor_set(v___x_745_, 2, v___x_742_);
return v___x_745_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__74(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__73, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__73_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__73);
v___x_747_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_748_ = lean_array_push(v___x_747_, v___x_746_);
return v___x_748_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__75(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__74, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__74_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__74);
v___x_750_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__69));
v___x_751_ = lean_box(2);
v___x_752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_749_);
return v___x_752_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__76(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__75, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__75_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__75);
v___x_754_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_755_ = lean_array_push(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__77(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_756_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__76, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__76_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__76);
v___x_757_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_758_ = lean_box(2);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
lean_ctor_set(v___x_759_, 2, v___x_756_);
return v___x_759_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__78(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__77, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__77_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__77);
v___x_761_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__24, &lp_GRH_New_LineBundle_cover___autoParam___closed__24_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__24);
v___x_762_ = lean_array_push(v___x_761_, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__79(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&lp_GRH_New_LineBundle_cover___autoParam___closed__66, &lp_GRH_New_LineBundle_cover___autoParam___closed__66_once, _init_lp_GRH_New_LineBundle_cover___autoParam___closed__66);
v___x_764_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__78, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__78_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__78);
v___x_765_ = lean_array_push(v___x_764_, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__80(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__79, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__79_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__79);
v___x_767_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_768_ = lean_box(2);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
lean_ctor_set(v___x_769_, 2, v___x_766_);
return v___x_769_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__81(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__80, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__80_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__80);
v___x_771_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__67, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__67_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__67);
v___x_772_ = lean_array_push(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__82(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__16));
v___x_774_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__81, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__81_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__81);
v___x_775_ = lean_array_push(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__83(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_776_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__82, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__82_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__82);
v___x_777_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__63));
v___x_778_ = lean_box(2);
v___x_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_777_);
lean_ctor_set(v___x_779_, 2, v___x_776_);
return v___x_779_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__84(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__83, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__83_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__83);
v___x_781_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__61, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__61_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__61);
v___x_782_ = lean_array_push(v___x_781_, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__85(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__84, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__84_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__84);
v___x_784_ = ((lean_object*)(lp_GRH_New_LineBundle_transition__trans___autoParam___closed__1));
v___x_785_ = lean_box(2);
v___x_786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_783_);
return v___x_786_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__86(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__85, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__85_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__85);
v___x_788_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_789_ = lean_array_push(v___x_788_, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__87(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__86, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__86_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__86);
v___x_791_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__9));
v___x_792_ = lean_box(2);
v___x_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
lean_ctor_set(v___x_793_, 2, v___x_790_);
return v___x_793_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__88(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__87, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__87_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__87);
v___x_795_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_796_ = lean_array_push(v___x_795_, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__89(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_797_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__88, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__88_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__88);
v___x_798_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__7));
v___x_799_ = lean_box(2);
v___x_800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_798_);
lean_ctor_set(v___x_800_, 2, v___x_797_);
return v___x_800_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__90(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__89, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__89_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__89);
v___x_802_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__5));
v___x_803_ = lean_array_push(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__91(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_804_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__90, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__90_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__90);
v___x_805_ = ((lean_object*)(lp_GRH_New_LineBundle_cover___autoParam___closed__4));
v___x_806_ = lean_box(2);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___x_805_);
lean_ctor_set(v___x_807_, 2, v___x_804_);
return v___x_807_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_transition__trans___autoParam(void){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&lp_GRH_New_LineBundle_transition__trans___autoParam___closed__91, &lp_GRH_New_LineBundle_transition__trans___autoParam___closed__91_once, _init_lp_GRH_New_LineBundle_transition__trans___autoParam___closed__91);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___lam__0(lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_813_; lean_object* v_toAddMonoidWithOne_814_; lean_object* v_toOne_815_; 
v___x_813_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___y_811_);
v_toAddMonoidWithOne_814_ = lean_ctor_get(v___x_813_, 1);
lean_inc_ref(v_toAddMonoidWithOne_814_);
lean_dec_ref(v___x_813_);
v_toOne_815_ = lean_ctor_get(v_toAddMonoidWithOne_814_, 2);
lean_inc(v_toOne_815_);
lean_dec_ref(v_toAddMonoidWithOne_814_);
return v_toOne_815_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___lam__0___boxed(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = lp_GRH_New_LineBundle_one___redArg___lam__0(v_x_816_, v_x_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___y_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___lam__1(lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_box(0);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg(){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = ((lean_object*)(lp_GRH_New_LineBundle_one___redArg___closed__2));
return v___x_829_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___redArg___boxed(lean_object* v___dummy_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = lp_GRH_New_LineBundle_one___redArg();
return v_res_831_;
}
}
static lean_object* _init_lp_GRH_New_LineBundle_one___closed__0(void){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lp_GRH_New_LineBundle_one___redArg();
return v___x_832_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one(lean_object* v_X_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_once(&lp_GRH_New_LineBundle_one___closed__0, &lp_GRH_New_LineBundle_one___closed__0_once, _init_lp_GRH_New_LineBundle_one___closed__0);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_one___boxed(lean_object* v_X_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = lp_GRH_New_LineBundle_one(v_X_835_);
lean_dec_ref(v_X_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv___redArg___lam__0(lean_object* v_transition_837_, lean_object* v_i_838_, lean_object* v_j_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_apply_4(v_transition_837_, v_j_839_, v_i_838_, v___y_840_, v___y_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv___redArg(lean_object* v_L_843_){
_start:
{
lean_object* v_opens_844_; lean_object* v_transition_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_opens_844_ = lean_ctor_get(v_L_843_, 0);
v_transition_845_ = lean_ctor_get(v_L_843_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_L_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_847_ = v_L_843_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_transition_845_);
lean_inc(v_opens_844_);
lean_dec(v_L_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___f_849_; lean_object* v___x_851_; 
v___f_849_ = lean_alloc_closure((void*)(lp_GRH_New_LineBundle_inv___redArg___lam__0), 5, 1);
lean_closure_set(v___f_849_, 0, v_transition_845_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___f_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_opens_844_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___f_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv(lean_object* v_X_854_, lean_object* v_00_u03b9_855_, lean_object* v_L_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lp_GRH_New_LineBundle_inv___redArg(v_L_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_inv___boxed(lean_object* v_X_858_, lean_object* v_00_u03b9_859_, lean_object* v_L_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = lp_GRH_New_LineBundle_inv(v_X_858_, v_00_u03b9_859_, v_L_860_);
lean_dec_ref(v_X_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg___lam__0(lean_object* v_L_862_, lean_object* v_M_863_, lean_object* v_i_864_, lean_object* v_j_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_transition_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v_transition_873_; lean_object* v_toSemiring_874_; lean_object* v___x_875_; lean_object* v_toMul_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_transition_868_ = lean_ctor_get(v_L_862_, 1);
lean_inc(v_transition_868_);
lean_dec_ref(v_L_862_);
v_fst_869_ = lean_ctor_get(v_i_864_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v_i_864_, 1);
lean_inc(v_snd_870_);
lean_dec_ref(v_i_864_);
v_fst_871_ = lean_ctor_get(v_j_865_, 0);
lean_inc(v_fst_871_);
v_snd_872_ = lean_ctor_get(v_j_865_, 1);
lean_inc(v_snd_872_);
lean_dec_ref(v_j_865_);
v_transition_873_ = lean_ctor_get(v_M_863_, 1);
lean_inc(v_transition_873_);
lean_dec_ref(v_M_863_);
v_toSemiring_874_ = lean_ctor_get(v___y_866_, 0);
lean_inc_ref(v_toSemiring_874_);
v___x_875_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_874_);
v_toMul_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_toMul_876_);
lean_dec_ref(v___x_875_);
lean_inc_ref(v___y_867_);
lean_inc_ref(v___y_866_);
v___x_877_ = lean_apply_4(v_transition_868_, v_fst_869_, v_fst_871_, v___y_866_, v___y_867_);
v___x_878_ = lean_apply_4(v_transition_873_, v_snd_870_, v_snd_872_, v___y_866_, v___y_867_);
v___x_879_ = lean_apply_2(v_toMul_876_, v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg___lam__1(lean_object* v_i_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_box(0);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg___lam__1___boxed(lean_object* v_i_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = lp_GRH_New_LineBundle_mul___redArg___lam__1(v_i_882_);
lean_dec_ref(v_i_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___redArg(lean_object* v_L_885_, lean_object* v_M_886_){
_start:
{
lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; 
v___f_887_ = lean_alloc_closure((void*)(lp_GRH_New_LineBundle_mul___redArg___lam__0), 6, 2);
lean_closure_set(v___f_887_, 0, v_L_885_);
lean_closure_set(v___f_887_, 1, v_M_886_);
v___f_888_ = ((lean_object*)(lp_GRH_New_LineBundle_mul___redArg___closed__0));
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___f_888_);
lean_ctor_set(v___x_889_, 1, v___f_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul(lean_object* v_X_890_, lean_object* v_00_u03b9_891_, lean_object* v_00_u03ba_892_, lean_object* v_L_893_, lean_object* v_M_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lp_GRH_New_LineBundle_mul___redArg(v_L_893_, v_M_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_mul___boxed(lean_object* v_X_896_, lean_object* v_00_u03b9_897_, lean_object* v_00_u03ba_898_, lean_object* v_L_899_, lean_object* v_M_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = lp_GRH_New_LineBundle_mul(v_X_896_, v_00_u03b9_897_, v_00_u03ba_898_, v_L_899_, v_M_900_);
lean_dec_ref(v_X_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0___redArg(){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_box(0);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0___redArg___boxed(lean_object* v___dummy_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = lp_GRH_New_LineBundle_H0___redArg();
return v_res_905_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0(lean_object* v_X_906_, lean_object* v_00_u03b9_907_, lean_object* v_L_908_, lean_object* v_R_909_, lean_object* v_inst_910_, lean_object* v_inst_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_box(0);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_H0___boxed(lean_object* v_X_913_, lean_object* v_00_u03b9_914_, lean_object* v_L_915_, lean_object* v_R_916_, lean_object* v_inst_917_, lean_object* v_inst_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = lp_GRH_New_LineBundle_H0(v_X_913_, v_00_u03b9_914_, v_L_915_, v_R_916_, v_inst_917_, v_inst_918_);
lean_dec(v_inst_918_);
lean_dec_ref(v_inst_917_);
lean_dec_ref(v_L_915_);
lean_dec_ref(v_X_913_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_picClass___redArg(lean_object* v_K_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, lean_box(0));
lean_ctor_set(v___x_921_, 1, v_K_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_picClass(lean_object* v_X_922_, lean_object* v_00_u03b9_923_, lean_object* v_K_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, lean_box(0));
lean_ctor_set(v___x_925_, 1, v_K_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LineBundle_picClass___boxed(lean_object* v_X_926_, lean_object* v_00_u03b9_927_, lean_object* v_K_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = lp_GRH_New_LineBundle_picClass(v_X_926_, v_00_u03b9_927_, v_K_928_);
lean_dec_ref(v_X_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___redArg___lam__0(lean_object* v_L_930_, lean_object* v_M_931_){
_start:
{
lean_object* v_snd_932_; lean_object* v_snd_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
v_snd_932_ = lean_ctor_get(v_L_930_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v_L_930_);
v_snd_933_ = lean_ctor_get(v_M_931_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_M_931_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_M_931_, 0);
lean_dec(v_unused_942_);
v___x_935_ = v_M_931_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_snd_933_);
lean_dec(v_M_931_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lp_GRH_New_LineBundle_mul___redArg(v_snd_932_, v_snd_933_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_937_);
lean_ctor_set(v___x_935_, 0, lean_box(0));
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, lean_box(0));
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___redArg(){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = ((lean_object*)(lp_GRH_New_instAddPic___redArg___closed__1));
return v___x_948_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___redArg___boxed(lean_object* v___dummy_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = lp_GRH_New_instAddPic___redArg();
return v_res_950_;
}
}
static lean_object* _init_lp_GRH_New_instAddPic___closed__0(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lp_GRH_New_instAddPic___redArg();
return v___x_951_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic(lean_object* v_X_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_obj_once(&lp_GRH_New_instAddPic___closed__0, &lp_GRH_New_instAddPic___closed__0_once, _init_lp_GRH_New_instAddPic___closed__0);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddPic___boxed(lean_object* v_X_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = lp_GRH_New_instAddPic(v_X_954_);
lean_dec_ref(v_X_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___redArg___lam__0(lean_object* v_L_956_){
_start:
{
lean_object* v_snd_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_snd_957_ = lean_ctor_get(v_L_956_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_L_956_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_L_956_, 0);
lean_dec(v_unused_966_);
v___x_959_ = v_L_956_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_snd_957_);
lean_dec(v_L_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lp_GRH_New_LineBundle_inv___redArg(v_snd_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___x_961_);
lean_ctor_set(v___x_959_, 0, lean_box(0));
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, lean_box(0));
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___redArg(){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(lp_GRH_New_instNegPic___redArg___closed__1));
return v___x_972_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___redArg___boxed(lean_object* v___dummy_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = lp_GRH_New_instNegPic___redArg();
return v_res_974_;
}
}
static lean_object* _init_lp_GRH_New_instNegPic___closed__0(void){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lp_GRH_New_instNegPic___redArg();
return v___x_975_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic(lean_object* v_X_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_obj_once(&lp_GRH_New_instNegPic___closed__0, &lp_GRH_New_instNegPic___closed__0_once, _init_lp_GRH_New_instNegPic___closed__0);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instNegPic___boxed(lean_object* v_X_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = lp_GRH_New_instNegPic(v_X_978_);
lean_dec_ref(v_X_978_);
return v_res_979_;
}
}
static lean_object* _init_lp_GRH_New_instZeroPic___redArg___closed__0(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_obj_once(&lp_GRH_New_LineBundle_one___closed__0, &lp_GRH_New_LineBundle_one___closed__0_once, _init_lp_GRH_New_LineBundle_one___closed__0);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, lean_box(0));
lean_ctor_set(v___x_981_, 1, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic___redArg(){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_obj_once(&lp_GRH_New_instZeroPic___redArg___closed__0, &lp_GRH_New_instZeroPic___redArg___closed__0_once, _init_lp_GRH_New_instZeroPic___redArg___closed__0);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic___redArg___boxed(lean_object* v___dummy_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = lp_GRH_New_instZeroPic___redArg();
return v_res_985_;
}
}
static lean_object* _init_lp_GRH_New_instZeroPic___closed__0(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lp_GRH_New_instZeroPic___redArg();
return v___x_986_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic(lean_object* v_X_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_obj_once(&lp_GRH_New_instZeroPic___closed__0, &lp_GRH_New_instZeroPic___closed__0_once, _init_lp_GRH_New_instZeroPic___closed__0);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instZeroPic___boxed(lean_object* v_X_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = lp_GRH_New_instZeroPic(v_X_989_);
lean_dec_ref(v_X_989_);
return v_res_990_;
}
}
static lean_object* _init_lp_GRH_New_instAddCommGroupPic___redArg___closed__0(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_obj_once(&lp_GRH_New_instZeroPic___closed__0, &lp_GRH_New_instZeroPic___closed__0_once, _init_lp_GRH_New_instZeroPic___closed__0);
v___x_992_ = lean_obj_once(&lp_GRH_New_instNegPic___closed__0, &lp_GRH_New_instNegPic___closed__0_once, _init_lp_GRH_New_instNegPic___closed__0);
v___x_993_ = lean_obj_once(&lp_GRH_New_instAddPic___closed__0, &lp_GRH_New_instAddPic___closed__0_once, _init_lp_GRH_New_instAddPic___closed__0);
v___x_994_ = lp_mathlib_AddGroup_ofRightAxioms___redArg(v___x_993_, v___x_992_, v___x_991_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic___redArg(){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_obj_once(&lp_GRH_New_instAddCommGroupPic___redArg___closed__0, &lp_GRH_New_instAddCommGroupPic___redArg___closed__0_once, _init_lp_GRH_New_instAddCommGroupPic___redArg___closed__0);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic___redArg___boxed(lean_object* v___dummy_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = lp_GRH_New_instAddCommGroupPic___redArg();
return v_res_998_;
}
}
static lean_object* _init_lp_GRH_New_instAddCommGroupPic___closed__0(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lp_GRH_New_instAddCommGroupPic___redArg();
return v___x_999_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic(lean_object* v_X_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&lp_GRH_New_instAddCommGroupPic___closed__0, &lp_GRH_New_instAddCommGroupPic___closed__0_once, _init_lp_GRH_New_instAddCommGroupPic___closed__0);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupPic___boxed(lean_object* v_X_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = lp_GRH_New_instAddCommGroupPic(v_X_1002_);
lean_dec_ref(v_X_1002_);
return v_res_1003_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Geometry_LineBundles(uint8_t builtin) {
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
lp_GRH_New_LineBundle_cover___autoParam = _init_lp_GRH_New_LineBundle_cover___autoParam();
lean_mark_persistent(lp_GRH_New_LineBundle_cover___autoParam);
lp_GRH_New_LineBundle_regular___autoParam = _init_lp_GRH_New_LineBundle_regular___autoParam();
lean_mark_persistent(lp_GRH_New_LineBundle_regular___autoParam);
lp_GRH_New_LineBundle_transition__self___autoParam = _init_lp_GRH_New_LineBundle_transition__self___autoParam();
lean_mark_persistent(lp_GRH_New_LineBundle_transition__self___autoParam);
lp_GRH_New_LineBundle_transition__trans___autoParam = _init_lp_GRH_New_LineBundle_transition__trans___autoParam();
lean_mark_persistent(lp_GRH_New_LineBundle_transition__trans___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
