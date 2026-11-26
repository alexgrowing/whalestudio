// Lean compiler output
// Module: Lib.Weil.Fock.OscillatorPair
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives public import Lib.Weil.Fock.PolynomialVectors
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__12 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__12_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__13;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__14;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__15_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__20;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__21 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__21_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__23 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__23_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rwRule"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__26 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__26_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(163, 12, 102, 31, 194, 63, 248, 122)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "continuous_U_iff_matrix"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__28 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__28_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__30;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(149, 75, 55, 89, 79, 241, 42, 214)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__31 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__31_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__32;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__33;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__34;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__35;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__36;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__37;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__38 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__38_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__40;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__41;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__42;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__43;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__44;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__45;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__46;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Mathlib"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__47 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__47_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__48 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__48_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunProp"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__49 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__49_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funPropTacStx"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__50 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__50_value;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(118, 213, 161, 2, 73, 184, 31, 228)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value_aux_0),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(210, 10, 180, 159, 248, 97, 218, 144)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value_aux_1),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 118, 4, 116, 28, 199, 219)}};
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value_aux_2),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(146, 162, 46, 139, 110, 137, 217, 136)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51_value;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fun_prop"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__52 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__52_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__53;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__54;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__55;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__56;
static const lean_string_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "kroneckerMap"};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__57 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__57_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__58;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__59;
static const lean_ctor_object lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(210, 253, 235, 186, 246, 10, 226, 114)}};
static const lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__60 = (const lean_object*)&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__60_value;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__61;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__62;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__63;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__64;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__65;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__66;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__67;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__68;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__69;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__70;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__71;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__72;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__73;
static lean_once_cell_t lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__74;
LEAN_EXPORT lean_object* lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1;
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__13(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__12));
v___x_29_ = l_Lean_mkAtom(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__14(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__13, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__13_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__13);
v___x_31_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_32_ = lean_array_push(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17));
v___x_44_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_45_ = lean_array_push(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_46_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18);
v___x_47_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__16));
v___x_48_ = lean_box(2);
v___x_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___x_47_);
lean_ctor_set(v___x_49_, 2, v___x_46_);
return v___x_49_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__20(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19);
v___x_51_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__14, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__14_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__14);
v___x_52_ = lean_array_push(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__24(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__23));
v___x_61_ = l_Lean_mkAtom(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__24, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__24_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__24);
v___x_63_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_64_ = lean_array_push(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__29(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__28));
v___x_73_ = lean_string_utf8_byte_size(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__30(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__29, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__29_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__29);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__28));
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
return v___x_77_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__32(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = lean_box(0);
v___x_81_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__31));
v___x_82_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__30, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__30_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__30);
v___x_83_ = lean_box(2);
v___x_84_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
lean_ctor_set(v___x_84_, 2, v___x_81_);
lean_ctor_set(v___x_84_, 3, v___x_80_);
return v___x_84_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__33(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__32, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__32_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__32);
v___x_86_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__18);
v___x_87_ = lean_array_push(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__34(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__33, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__33_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__33);
v___x_89_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__27));
v___x_90_ = lean_box(2);
v___x_91_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
return v___x_91_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__35(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__34, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__34_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__34);
v___x_93_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_94_ = lean_array_push(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__36(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__35, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__35_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__35);
v___x_96_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9));
v___x_97_ = lean_box(2);
v___x_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_95_);
return v___x_98_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__37(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__36, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__36_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__36);
v___x_100_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25);
v___x_101_ = lean_array_push(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__38));
v___x_104_ = l_Lean_mkAtom(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__40(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39);
v___x_106_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__37, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__37_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__37);
v___x_107_ = lean_array_push(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__41(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__40, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__40_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__40);
v___x_109_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__22));
v___x_110_ = lean_box(2);
v___x_111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_108_);
return v___x_111_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__42(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__41, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__41_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__41);
v___x_113_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__20, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__20_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__20);
v___x_114_ = lean_array_push(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__43(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17));
v___x_116_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__42, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__42_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__42);
v___x_117_ = lean_array_push(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__44(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__43, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__43_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__43);
v___x_119_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__11));
v___x_120_ = lean_box(2);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__45(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__44, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__44_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__44);
v___x_123_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__46(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17));
v___x_126_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__45, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__45_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__45);
v___x_127_ = lean_array_push(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__53(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__52));
v___x_139_ = l_Lean_mkAtom(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__54(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__53, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__53_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__53);
v___x_141_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_142_ = lean_array_push(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__55(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__19);
v___x_144_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__54, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__54_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__54);
v___x_145_ = lean_array_push(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__56(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__17));
v___x_147_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__55, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__55_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__55);
v___x_148_ = lean_array_push(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__58(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__57));
v___x_151_ = lean_string_utf8_byte_size(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__59(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__58, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__58_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__58);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__57));
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_152_);
return v___x_155_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__61(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = lean_box(0);
v___x_159_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__60));
v___x_160_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__59, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__59_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__59);
v___x_161_ = lean_box(2);
v___x_162_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_159_);
lean_ctor_set(v___x_162_, 3, v___x_158_);
return v___x_162_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__62(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__61, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__61_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__61);
v___x_164_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_165_ = lean_array_push(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__63(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__62, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__62_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__62);
v___x_167_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9));
v___x_168_ = lean_box(2);
v___x_169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_166_);
return v___x_169_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__64(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__63, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__63_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__63);
v___x_171_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__25);
v___x_172_ = lean_array_push(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__65(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__39);
v___x_174_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__64, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__64_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__64);
v___x_175_ = lean_array_push(v___x_174_, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__66(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__65, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__65_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__65);
v___x_177_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9));
v___x_178_ = lean_box(2);
v___x_179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
lean_ctor_set(v___x_179_, 2, v___x_176_);
return v___x_179_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__67(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__66, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__66_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__66);
v___x_181_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__56, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__56_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__56);
v___x_182_ = lean_array_push(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__68(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__67, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__67_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__67);
v___x_184_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__51));
v___x_185_ = lean_box(2);
v___x_186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_183_);
return v___x_186_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__69(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__68, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__68_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__68);
v___x_188_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__46, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__46_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__46);
v___x_189_ = lean_array_push(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__70(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_190_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__69, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__69_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__69);
v___x_191_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__9));
v___x_192_ = lean_box(2);
v___x_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
lean_ctor_set(v___x_193_, 2, v___x_190_);
return v___x_193_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__71(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__70, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__70_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__70);
v___x_195_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_196_ = lean_array_push(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__72(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_197_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__71, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__71_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__71);
v___x_198_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__7));
v___x_199_ = lean_box(2);
v___x_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
lean_ctor_set(v___x_200_, 2, v___x_197_);
return v___x_200_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__73(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__72, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__72_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__72);
v___x_202_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__5));
v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__74(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__73, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__73_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__73);
v___x_205_ = ((lean_object*)(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__4));
v___x_206_ = lean_box(2);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
return v___x_207_;
}
}
static lean_object* _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__74, &lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__74_once, _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1___closed__74);
return v___x_208_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_RightDerivatives(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Fock_PolynomialVectors(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Fock_OscillatorPair(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_RightDerivatives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Fock_PolynomialVectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1 = _init_lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1();
lean_mark_persistent(lp_GRH_New_Fock_isUnitaryRep__detTwist___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
