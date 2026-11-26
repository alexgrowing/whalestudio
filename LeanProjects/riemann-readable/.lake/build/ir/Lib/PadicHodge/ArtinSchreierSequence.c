// Lean compiler output
// Module: Lib.PadicHodge.ArtinSchreierSequence
// Imports: public import Init public meta import Init public import Lib.PadicHodge.Kisin.KummerChartExistence
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
lean_object* lean_string_utf8_byte_size(lean_object*);
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__12 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__12_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__14;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__15;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__16_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__18 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__18_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__20 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__20_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21_value;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__22 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__22_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__24;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "contextual"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__25 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__25_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__26;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__27;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(229, 190, 84, 18, 151, 13, 33, 25)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__28 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__28_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__32;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__33;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__34;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__35;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__36;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__37;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__38;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__40;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__41;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__42;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__43;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__44;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__45;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__46 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__46_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__47;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__48;
static const lean_string_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__49 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__49_value;
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value_aux_0),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value_aux_1),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value_aux_2),((lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50 = (const lean_object*)&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50_value;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__51;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__52;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__53;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__54;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__55;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__56;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__57;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__58;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__59;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__60;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__61;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__62;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__63;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__64;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__65;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__66;
static lean_once_cell_t lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__67;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_diagTensor__induction___auto__1;
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__14(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__12));
v___x_34_ = l_Lean_mkAtom(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__15(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__14, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__14_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__14);
v___x_36_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_37_ = lean_array_push(v___x_36_, v___x_35_);
return v___x_37_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__23(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__22));
v___x_58_ = l_Lean_mkAtom(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__24(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__23, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__23_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__23);
v___x_60_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_61_ = lean_array_push(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__26(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__25));
v___x_64_ = lean_string_utf8_byte_size(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__27(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__26, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__26_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__26);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__25));
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_65_);
return v___x_68_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__29(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_71_ = lean_box(0);
v___x_72_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__28));
v___x_73_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__27, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__27_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__27);
v___x_74_ = lean_box(2);
v___x_75_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
lean_ctor_set(v___x_75_, 3, v___x_71_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__30(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__29, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__29_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__29);
v___x_77_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__24, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__24_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__24);
v___x_78_ = lean_array_push(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__31(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__30, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__30_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__30);
v___x_80_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__21));
v___x_81_ = lean_box(2);
v___x_82_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
lean_ctor_set(v___x_82_, 2, v___x_79_);
return v___x_82_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__32(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__31, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__31_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__31);
v___x_84_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_85_ = lean_array_push(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__33(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__32, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__32_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__32);
v___x_87_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__19));
v___x_88_ = lean_box(2);
v___x_89_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_86_);
return v___x_89_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__34(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__33, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__33_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__33);
v___x_91_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_92_ = lean_array_push(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__35(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__34, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__34_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__34);
v___x_94_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__9));
v___x_95_ = lean_box(2);
v___x_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__36(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__35, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__35_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__35);
v___x_98_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__37(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__36, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__36_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__36);
v___x_101_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17));
v___x_102_ = lean_box(2);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__38(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__37, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__37_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__37);
v___x_105_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__15, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__15_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__15);
v___x_106_ = lean_array_push(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__40(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_112_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__38, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__38_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__38);
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__41(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_115_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__40, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__40_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__40);
v___x_116_ = lean_array_push(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__42(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_118_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__41, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__41_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__41);
v___x_119_ = lean_array_push(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__43(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_121_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__42, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__42_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__42);
v___x_122_ = lean_array_push(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__44(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__43, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__43_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__43);
v___x_124_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__13));
v___x_125_ = lean_box(2);
v___x_126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
lean_ctor_set(v___x_126_, 2, v___x_123_);
return v___x_126_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__45(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__44, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__44_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__44);
v___x_128_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_129_ = lean_array_push(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__47(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__46));
v___x_132_ = l_Lean_mkAtom(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__48(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__47, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__47_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__47);
v___x_134_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__45, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__45_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__45);
v___x_135_ = lean_array_push(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__51(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__49));
v___x_143_ = l_Lean_mkAtom(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__52(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__51, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__51_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__51);
v___x_145_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__53(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_148_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_149_ = lean_array_push(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__54(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__53, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__53_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__53);
v___x_151_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__17));
v___x_152_ = lean_box(2);
v___x_153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_150_);
return v___x_153_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__55(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__54, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__54_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__54);
v___x_155_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__52, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__52_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__52);
v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__56(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_158_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__55, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__55_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__55);
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__57(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_161_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__56, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__56_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__56);
v___x_162_ = lean_array_push(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__58(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__39));
v___x_164_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__57, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__57_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__57);
v___x_165_ = lean_array_push(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__59(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__58, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__58_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__58);
v___x_167_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__50));
v___x_168_ = lean_box(2);
v___x_169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_166_);
return v___x_169_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__60(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__59, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__59_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__59);
v___x_171_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__48, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__48_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__48);
v___x_172_ = lean_array_push(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__61(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__60, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__60_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__60);
v___x_174_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__11));
v___x_175_ = lean_box(2);
v___x_176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
return v___x_176_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__62(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__61, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__61_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__61);
v___x_178_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_179_ = lean_array_push(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__63(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__62, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__62_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__62);
v___x_181_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__9));
v___x_182_ = lean_box(2);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_180_);
return v___x_183_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__64(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__63, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__63_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__63);
v___x_185_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_186_ = lean_array_push(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__65(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_187_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__64, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__64_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__64);
v___x_188_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__7));
v___x_189_ = lean_box(2);
v___x_190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_187_);
return v___x_190_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__66(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__65, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__65_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__65);
v___x_192_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__5));
v___x_193_ = lean_array_push(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__67(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__66, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__66_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__66);
v___x_195_ = ((lean_object*)(lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__4));
v___x_196_ = lean_box(2);
v___x_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
lean_ctor_set(v___x_197_, 2, v___x_194_);
return v___x_197_;
}
}
static lean_object* _init_lp_GRH_New_Lift_diagTensor__induction___auto__1(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__67, &lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__67_once, _init_lp_GRH_New_Lift_diagTensor__induction___auto__1___closed__67);
return v___x_198_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Kisin_KummerChartExistence(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicHodge_ArtinSchreierSequence(uint8_t builtin) {
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
res = initialize_GRH_Lib_PadicHodge_Kisin_KummerChartExistence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Lift_diagTensor__induction___auto__1 = _init_lp_GRH_New_Lift_diagTensor__induction___auto__1();
lean_mark_persistent(lp_GRH_New_Lift_diagTensor__induction___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
