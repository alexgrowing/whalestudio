// Lean compiler output
// Module: Lib.DiscreteSeries.Bruhat.FloorMeasures
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bruhat.FloorGroups public import Lib.General.Measure.IntegralOperators public import Lib.General.Measure.QuadricDisintegration
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lp_GRH_New_inclMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_PUnit_fintype;
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(41, 145, 9, 18, 75, 146, 159, 78)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11_value;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__13;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14_value;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__15;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__16;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__17;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__18 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__18_value;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__19;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__20;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__21 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__21_value;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value_aux_0),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value_aux_1),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value_aux_2),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22_value;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__24;
static const lean_string_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__25 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__25_value;
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value_aux_0),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value_aux_1),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value_aux_2),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26 = (const lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26_value;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__27;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__28;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__32;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__33;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__35;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__36;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__37;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__38;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__39;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__40;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__0;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__1;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__2;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__3;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__4;
static lean_once_cell_t lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__5;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_middleVector___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_middleVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_middleVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__7(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__8(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__9(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__10(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__11(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__12(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__13(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__14(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__15(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__15___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__16(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__17(lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__20___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__0_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__5, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__2_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__6, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__3 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__3_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__7, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__4 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__4_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__8, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__5 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__5_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__9, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__6 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__6_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__10, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__7 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__7_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__11, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__8 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__8_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__12, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__9 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__9_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__13, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__10 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__10_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__14, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__11 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__11_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__15___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__12 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__12_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__16, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__13 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__13_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__17, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__14 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__14_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__14_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__13_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__15 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__15_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__11_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__12_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__16 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__16_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_map, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__12_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__16_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__17 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__17_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__15_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__17_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__18 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__18_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__10_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__9_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__19 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__19_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__8_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__7_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__20 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__20_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_map, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__20_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__6_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__21 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__21_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__5_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__4_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__22 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__22_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__8_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__22_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__23 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__23_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__10_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__23_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__24 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__24_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__5_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__3_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__25 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__25_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__8_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__25_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__26 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__26_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_map, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__26_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__2_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__27 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__27_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__24_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__27_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__28 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__28_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__21_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__28_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__29 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__29_value;
static const lean_closure_object lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__19_value),((lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__29_value)} };
static const lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__30 = (const lean_object*)&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__30_value;
static lean_once_cell_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__31;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__0_value;
static const lean_ctor_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value_aux_0),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value_aux_1),((lean_object*)&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value_aux_2),((lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1_value;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__2;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__3;
static const lean_string_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "measurableSet_floorGroup"};
static const lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__4_value;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__5;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__6;
static const lean_ctor_object lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 117, 20, 254, 238, 31, 178, 180)}};
static const lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__7_value;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__8;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__9;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__10;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__11;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__13;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__14;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__15;
static lean_once_cell_t lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__16;
LEAN_EXPORT lean_object* lp_GRH_New_Floors_ae__mem__mconv___auto__1;
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__12, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__12_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__12);
v___x_30_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__15(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14));
v___x_37_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__13, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__13_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__13);
v___x_38_ = lean_array_push(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__16(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__15, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__15_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__15);
v___x_40_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__11));
v___x_41_ = lean_box(2);
v___x_42_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__17(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__16, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__16_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__16);
v___x_44_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_45_ = lean_array_push(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__18));
v___x_48_ = l_Lean_mkAtom(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__19, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__19_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__19);
v___x_50_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__17, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__17_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__17);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__23(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__21));
v___x_59_ = l_Lean_mkAtom(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__24(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__23, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__23_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__23);
v___x_61_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__27(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14));
v___x_70_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_71_ = lean_array_push(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__28(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__27, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__27_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__27);
v___x_73_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__26));
v___x_74_ = lean_box(2);
v___x_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__29(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__28, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__28_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__28);
v___x_77_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__24, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__24_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__24);
v___x_78_ = lean_array_push(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__30(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14));
v___x_80_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__29, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__29_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__29);
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__31(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14));
v___x_83_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__30, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__30_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__30);
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__32(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14));
v___x_86_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__31, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__31_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__31);
v___x_87_ = lean_array_push(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__33(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__14));
v___x_89_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__32, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__32_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__32);
v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__33, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__33_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__33);
v___x_92_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__22));
v___x_93_ = lean_box(2);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__35(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34);
v___x_96_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__20, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__20_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__20);
v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__36(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__35, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__35_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__35);
v___x_99_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9));
v___x_100_ = lean_box(2);
v___x_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__37(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__36, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__36_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__36);
v___x_103_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_104_ = lean_array_push(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__38(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__37, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__37_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__37);
v___x_106_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7));
v___x_107_ = lean_box(2);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__39(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__38, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__38_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__38);
v___x_110_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__40(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__39, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__39_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__39);
v___x_113_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4));
v___x_114_ = lean_box(2);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__40, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__40_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__40);
return v___x_116_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__0(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__34);
v___x_118_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_119_ = lean_array_push(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__1(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__0, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__0_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__0);
v___x_121_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9));
v___x_122_ = lean_box(2);
v___x_123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__2(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__1, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__1_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__1);
v___x_125_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__3(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__2, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__2_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__2);
v___x_128_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7));
v___x_129_ = lean_box(2);
v___x_130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__4(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__3, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__3_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__3);
v___x_132_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_133_ = lean_array_push(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__5(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__4, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__4_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__4);
v___x_135_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4));
v___x_136_ = lean_box(2);
v___x_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__5, &lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__5_once, _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3___closed__5);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_middleVector___redArg(lean_object* v_inst_139_, lean_object* v_F_140_, lean_object* v_j_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_toSemiring_143_; lean_object* v___x_144_; 
v_toSemiring_143_ = lean_ctor_get(v_inst_139_, 0);
lean_inc_ref(v_toSemiring_143_);
lean_dec_ref(v_inst_139_);
v___x_144_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_143_);
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v_toZero_145_; 
lean_dec_ref_known(v_x_142_, 1);
lean_dec_ref(v_j_141_);
lean_dec(v_F_140_);
v_toZero_145_ = lean_ctor_get(v___x_144_, 1);
lean_inc(v_toZero_145_);
lean_dec_ref(v___x_144_);
return v_toZero_145_;
}
else
{
lean_object* v_val_146_; 
v_val_146_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_val_146_);
lean_dec_ref_known(v_x_142_, 1);
if (lean_obj_tag(v_val_146_) == 0)
{
lean_object* v_val_147_; lean_object* v___x_148_; 
lean_dec_ref(v___x_144_);
v_val_147_ = lean_ctor_get(v_val_146_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v_val_146_, 1);
v___x_148_ = lean_apply_2(v_F_140_, v_val_147_, v_j_141_);
return v___x_148_;
}
else
{
lean_object* v_toZero_149_; 
lean_dec_ref_known(v_val_146_, 1);
lean_dec_ref(v_j_141_);
lean_dec(v_F_140_);
v_toZero_149_ = lean_ctor_get(v___x_144_, 1);
lean_inc(v_toZero_149_);
lean_dec_ref(v___x_144_);
return v_toZero_149_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_middleVector(lean_object* v_A_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_00_U0001d530_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_P_156_, lean_object* v_00_u03b9_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_T_160_, lean_object* v_m_161_, lean_object* v_F_162_, lean_object* v_j_163_, lean_object* v_x_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lp_GRH_New_Floors_HyperbolicBasis_middleVector___redArg(v_inst_151_, v_F_162_, v_j_163_, v_x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_middleVector___boxed(lean_object* v_A_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_00_U0001d530_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_P_172_, lean_object* v_00_u03b9_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_T_176_, lean_object* v_m_177_, lean_object* v_F_178_, lean_object* v_j_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = lp_GRH_New_Floors_HyperbolicBasis_middleVector(v_A_166_, v_inst_167_, v_inst_168_, v_00_U0001d530_169_, v_inst_170_, v_inst_171_, v_P_172_, v_00_u03b9_173_, v_inst_174_, v_inst_175_, v_T_176_, v_m_177_, v_F_178_, v_j_179_, v_x_180_);
lean_dec(v_m_177_);
lean_dec(v_T_176_);
lean_dec_ref(v_inst_175_);
lean_dec(v_inst_174_);
lean_dec_ref(v_P_172_);
lean_dec_ref(v_inst_171_);
lean_dec_ref(v_00_U0001d530_169_);
lean_dec(v_inst_168_);
return v_res_181_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__0(lean_object* v___f_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
uint8_t v___x_185_; 
lean_inc_ref(v___f_182_);
v___x_185_ = l_instDecidableEqSum_decEq___redArg(v___f_182_, v___f_182_, v_a_183_, v_b_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__0___boxed(lean_object* v___f_186_, lean_object* v_a_187_, lean_object* v_b_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__0(v___f_186_, v_a_187_, v_b_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__1(lean_object* v_inst_191_, lean_object* v___x_192_, lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = l_instDecidableEqSum_decEq___redArg(v_inst_191_, v___x_192_, v_a_193_, v_b_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__1___boxed(lean_object* v_inst_196_, lean_object* v___x_197_, lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__1(v_inst_196_, v___x_197_, v_a_198_, v_b_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__2(lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___f_207_; uint8_t v___x_208_; 
v___x_206_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_206_, 0, v_m_202_);
lean_inc_ref(v___x_206_);
v___f_207_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_207_, 0, v_inst_203_);
lean_closure_set(v___f_207_, 1, v___x_206_);
v___x_208_ = l_instDecidableEqSum_decEq___redArg(v___x_206_, v___f_207_, v_a_204_, v_b_205_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__2___boxed(lean_object* v_m_209_, lean_object* v_inst_210_, lean_object* v_a_211_, lean_object* v_b_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__2(v_m_209_, v_inst_210_, v_a_211_, v_b_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__3(lean_object* v_decEqIndex_215_, lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_219_ = l_instDecidableEqSum_decEq___redArg(v_decEqIndex_215_, v___x_218_, v_a_216_, v_b_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__3___boxed(lean_object* v_decEqIndex_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__3(v_decEqIndex_220_, v_a_221_, v_b_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__4(lean_object* v_b_225_, lean_object* v_a_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_le(v_b_225_, v_a_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__4___boxed(lean_object* v_b_228_, lean_object* v_a_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__4(v_b_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec(v_b_228_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__5(lean_object* v_val_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_val_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__6(lean_object* v_val_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_val_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__7(lean_object* v_val_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_val_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__8(lean_object* v_val_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_val_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__9(lean_object* v_val_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v_val_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__10(lean_object* v_val_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_val_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__11(lean_object* v_val_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v_val_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__12(lean_object* v_val_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v_val_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__13(lean_object* v_val_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_val_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__14(lean_object* v_val_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_val_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__15(lean_object* v_self_252_){
_start:
{
lean_inc(v_self_252_);
return v_self_252_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__15___boxed(lean_object* v_self_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__15(v_self_253_);
lean_dec(v_self_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__16(lean_object* v_val_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_val_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__17(lean_object* v_val_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_val_257_);
return v___x_258_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__18(lean_object* v___f_259_, lean_object* v___x_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = l_instDecidableEqSum_decEq___redArg(v___f_259_, v___x_260_, v_a_261_, v_b_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__18___boxed(lean_object* v___f_264_, lean_object* v___x_265_, lean_object* v_a_266_, lean_object* v_b_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__18(v___f_264_, v___x_265_, v_a_266_, v_b_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__19(lean_object* v_00_u03f1_270_, lean_object* v___f_271_, lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___f_275_; uint8_t v___x_276_; 
v___x_274_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_274_, 0, v_00_u03f1_270_);
lean_inc_ref(v___x_274_);
v___f_275_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_275_, 0, v___f_271_);
lean_closure_set(v___f_275_, 1, v___x_274_);
v___x_276_ = l_instDecidableEqSum_decEq___redArg(v___x_274_, v___f_275_, v_a_272_, v_b_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__19___boxed(lean_object* v_00_u03f1_277_, lean_object* v___f_278_, lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__19(v_00_u03f1_277_, v___f_278_, v_a_279_, v_b_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__20(lean_object* v_toOne_283_, lean_object* v_x_284_){
_start:
{
lean_inc(v_toOne_283_);
return v_toOne_283_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__20___boxed(lean_object* v_toOne_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__20(v_toOne_285_, v_x_286_);
lean_dec_ref(v_x_286_);
lean_dec(v_toOne_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__21(lean_object* v___f_288_, lean_object* v_toZero_289_, lean_object* v_toOne_290_, lean_object* v_incl_291_, lean_object* v_a_292_, lean_object* v_j_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lp_GRH_New_inclMatrix___redArg(v___f_288_, v_toZero_289_, v_toOne_290_, v_incl_291_, v_a_292_, v_j_293_);
return v___x_294_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__22(lean_object* v___x_295_, lean_object* v___f_296_, lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_299_, 0, v___x_295_);
v___x_300_ = l_instDecidableEqSum_decEq___redArg(v___x_299_, v___f_296_, v_a_297_, v_b_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__22___boxed(lean_object* v___x_301_, lean_object* v___f_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__22(v___x_301_, v___f_302_, v_a_303_, v_b_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__23(lean_object* v___f_307_, lean_object* v___f_308_, lean_object* v_a_309_, lean_object* v_b_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_instDecidableEqSum_decEq___redArg(v___f_307_, v___f_308_, v_a_309_, v_b_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__23___boxed(lean_object* v___f_312_, lean_object* v___f_313_, lean_object* v_a_314_, lean_object* v_b_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__23(v___f_312_, v___f_313_, v_a_314_, v_b_315_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__24(lean_object* v___f_318_, lean_object* v_toZero_319_, lean_object* v_toOne_320_, lean_object* v_order_321_, lean_object* v_a_322_, lean_object* v_j_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lp_GRH_New_inclMatrix___redArg(v___f_318_, v_toZero_319_, v_toOne_320_, v_order_321_, v_j_323_, v_a_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__25(lean_object* v_F_325_, lean_object* v___x_326_, lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v_j_329_, lean_object* v_j_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lp_mathlib_Matrix_fromBlocks___redArg(v_F_325_, v___x_326_, v___x_327_, v___x_328_, v_j_330_, v_j_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__26(lean_object* v_F_332_, lean_object* v___x_333_, lean_object* v___x_334_, lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v_toMul_337_, lean_object* v_toAddCommMonoid_338_, lean_object* v___f_339_, lean_object* v_j_340_){
_start:
{
lean_object* v___f_341_; lean_object* v___x_342_; 
v___f_341_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__25), 6, 5);
lean_closure_set(v___f_341_, 0, v_F_332_);
lean_closure_set(v___f_341_, 1, v___x_333_);
lean_closure_set(v___f_341_, 2, v___x_334_);
lean_closure_set(v___f_341_, 3, v___x_335_);
lean_closure_set(v___f_341_, 4, v_j_340_);
v___x_342_ = lp_mathlib_dotProduct___redArg(v___x_336_, v_toMul_337_, v_toAddCommMonoid_338_, v___f_339_, v___f_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__26___boxed(lean_object* v_F_343_, lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v_toMul_348_, lean_object* v_toAddCommMonoid_349_, lean_object* v___f_350_, lean_object* v_j_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__26(v_F_343_, v___x_344_, v___x_345_, v___x_346_, v___x_347_, v_toMul_348_, v_toAddCommMonoid_349_, v___f_350_, v_j_351_);
lean_dec_ref(v_toAddCommMonoid_349_);
return v_res_352_;
}
}
static lean_object* _init_lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__31(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(2u);
v___x_418_ = l_List_finRange(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg(lean_object* v_inst_419_, lean_object* v_00_U0001d530_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_m_423_, lean_object* v_F_424_, lean_object* v_b_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_toSemiring_428_; lean_object* v___x_429_; lean_object* v_toMul_430_; lean_object* v_toAddCommMonoid_431_; lean_object* v_00_u03f1_432_; lean_object* v_fintypeIndex_433_; lean_object* v_decEqIndex_434_; lean_object* v___x_435_; lean_object* v_toZero_436_; lean_object* v___x_437_; lean_object* v_toAddMonoidWithOne_438_; lean_object* v_toOne_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___f_450_; lean_object* v_incl_451_; lean_object* v___f_452_; lean_object* v_order_453_; lean_object* v___x_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___f_467_; lean_object* v___x_468_; 
v_toSemiring_428_ = lean_ctor_get(v_inst_419_, 0);
lean_inc_ref_n(v_toSemiring_428_, 2);
v___x_429_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_428_);
v_toMul_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_n(v_toMul_430_, 2);
lean_dec_ref(v___x_429_);
v_toAddCommMonoid_431_ = lean_ctor_get(v_toSemiring_428_, 0);
lean_inc_ref_n(v_toAddCommMonoid_431_, 2);
v_00_u03f1_432_ = lean_ctor_get(v_00_U0001d530_420_, 0);
lean_inc_n(v_00_u03f1_432_, 2);
v_fintypeIndex_433_ = lean_ctor_get(v_00_U0001d530_420_, 1);
lean_inc(v_fintypeIndex_433_);
v_decEqIndex_434_ = lean_ctor_get(v_00_U0001d530_420_, 2);
lean_inc_ref(v_decEqIndex_434_);
lean_dec_ref(v_00_U0001d530_420_);
v___x_435_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_428_);
v_toZero_436_ = lean_ctor_get(v___x_435_, 1);
lean_inc_n(v_toZero_436_, 4);
lean_dec_ref(v___x_435_);
v___x_437_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_419_);
v_toAddMonoidWithOne_438_ = lean_ctor_get(v___x_437_, 1);
lean_inc_ref(v_toAddMonoidWithOne_438_);
lean_dec_ref(v___x_437_);
v_toOne_439_ = lean_ctor_get(v_toAddMonoidWithOne_438_, 2);
lean_inc_n(v_toOne_439_, 3);
lean_dec_ref(v_toAddMonoidWithOne_438_);
lean_inc(v_m_423_);
v___x_440_ = l_List_finRange(v_m_423_);
lean_inc(v___x_440_);
v___x_441_ = lp_mathlib_Multiset_disjSum___redArg(v_inst_421_, v___x_440_);
v___f_442_ = ((lean_object*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__1));
v___f_443_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_443_, 0, v_m_423_);
lean_closure_set(v___f_443_, 1, v_inst_422_);
v___f_444_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_444_, 0, v_decEqIndex_434_);
v___f_445_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_445_, 0, v_b_425_);
v___x_446_ = lp_mathlib_PUnit_fintype;
v___x_447_ = lp_mathlib_Multiset_disjSum___redArg(v___x_440_, v___x_441_);
v___f_448_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__19___boxed), 4, 2);
lean_closure_set(v___f_448_, 0, v_00_u03f1_432_);
lean_closure_set(v___f_448_, 1, v___f_444_);
v___x_449_ = lp_mathlib_Multiset_disjSum___redArg(v_fintypeIndex_433_, v___x_446_);
v___f_450_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__20___boxed), 2, 1);
lean_closure_set(v___f_450_, 0, v_toOne_439_);
v_incl_451_ = ((lean_object*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__18));
v___f_452_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__21), 6, 5);
lean_closure_set(v___f_452_, 0, v___f_448_);
lean_closure_set(v___f_452_, 1, v_toZero_436_);
lean_closure_set(v___f_452_, 2, v_toOne_439_);
lean_closure_set(v___f_452_, 3, v_incl_451_);
lean_closure_set(v___f_452_, 4, v_a_426_);
v_order_453_ = ((lean_object*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__30));
v___x_454_ = lean_unsigned_to_nat(2u);
v___f_455_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__22___boxed), 4, 2);
lean_closure_set(v___f_455_, 0, v___x_454_);
lean_closure_set(v___f_455_, 1, v___f_443_);
v___f_456_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_456_, 0, v___f_455_);
lean_closure_set(v___f_456_, 1, v___f_442_);
v___f_457_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__24), 6, 5);
lean_closure_set(v___f_457_, 0, v___f_456_);
lean_closure_set(v___f_457_, 1, v_toZero_436_);
lean_closure_set(v___f_457_, 2, v_toOne_439_);
lean_closure_set(v___f_457_, 3, v_order_453_);
lean_closure_set(v___f_457_, 4, v_a_427_);
v___x_458_ = lean_obj_once(&lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__31, &lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__31_once, _init_lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___closed__31);
v___x_459_ = lp_mathlib_Multiset_disjSum___redArg(v___x_458_, v___x_447_);
v___x_460_ = l_List_finRange(v_00_u03f1_432_);
v___x_461_ = lp_mathlib_Subtype_fintype___redArg(v___f_445_, v___x_460_);
lean_inc(v___x_461_);
v___x_462_ = lp_mathlib_Multiset_disjSum___redArg(v___x_461_, v___x_461_);
lean_inc(v___x_462_);
v___x_463_ = lp_mathlib_Multiset_disjSum___redArg(v___x_459_, v___x_462_);
v___x_464_ = lp_mathlib_Multiset_disjSum___redArg(v___x_449_, v___x_462_);
v___x_465_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_465_, 0, lean_box(0));
lean_closure_set(v___x_465_, 1, lean_box(0));
lean_closure_set(v___x_465_, 2, lean_box(0));
lean_closure_set(v___x_465_, 3, v_toZero_436_);
v___x_466_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_466_, 0, lean_box(0));
lean_closure_set(v___x_466_, 1, lean_box(0));
lean_closure_set(v___x_466_, 2, v___f_442_);
lean_closure_set(v___x_466_, 3, v_toZero_436_);
lean_closure_set(v___x_466_, 4, v___f_450_);
lean_inc_ref(v___x_465_);
v___f_467_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg___lam__26___boxed), 9, 8);
lean_closure_set(v___f_467_, 0, v_F_424_);
lean_closure_set(v___f_467_, 1, v___x_465_);
lean_closure_set(v___f_467_, 2, v___x_465_);
lean_closure_set(v___f_467_, 3, v___x_466_);
lean_closure_set(v___f_467_, 4, v___x_464_);
lean_closure_set(v___f_467_, 5, v_toMul_430_);
lean_closure_set(v___f_467_, 6, v_toAddCommMonoid_431_);
lean_closure_set(v___f_467_, 7, v___f_452_);
v___x_468_ = lp_mathlib_dotProduct___redArg(v___x_463_, v_toMul_430_, v_toAddCommMonoid_431_, v___f_467_, v___f_457_);
lean_dec_ref(v_toAddCommMonoid_431_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis(lean_object* v_A_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_00_U0001d530_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_P_475_, lean_object* v_00_u03b9_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_T_479_, lean_object* v_m_480_, lean_object* v_F_481_, lean_object* v_b_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis___redArg(v_inst_470_, v_00_U0001d530_472_, v_inst_477_, v_inst_478_, v_m_480_, v_F_481_, v_b_482_, v_a_483_, v_a_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_HyperbolicBasis_floorBasis___boxed(lean_object* v_A_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_00_U0001d530_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_P_492_, lean_object* v_00_u03b9_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_T_496_, lean_object* v_m_497_, lean_object* v_F_498_, lean_object* v_b_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = lp_GRH_New_Floors_HyperbolicBasis_floorBasis(v_A_486_, v_inst_487_, v_inst_488_, v_00_U0001d530_489_, v_inst_490_, v_inst_491_, v_P_492_, v_00_u03b9_493_, v_inst_494_, v_inst_495_, v_T_496_, v_m_497_, v_F_498_, v_b_499_, v_a_500_, v_a_501_);
lean_dec(v_T_496_);
lean_dec_ref(v_P_492_);
lean_dec_ref(v_inst_491_);
lean_dec(v_inst_488_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter___redArg(lean_object* v_x_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_, lean_object* v_h__3_506_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v_val_507_; lean_object* v___x_508_; 
lean_dec(v_h__3_506_);
lean_dec(v_h__2_505_);
v_val_507_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v_x_503_, 1);
v___x_508_ = lean_apply_1(v_h__1_504_, v_val_507_);
return v___x_508_;
}
else
{
lean_object* v_val_509_; 
lean_dec(v_h__1_504_);
v_val_509_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_x_503_, 1);
if (lean_obj_tag(v_val_509_) == 0)
{
lean_object* v_val_510_; lean_object* v___x_511_; 
lean_dec(v_h__3_506_);
v_val_510_ = lean_ctor_get(v_val_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v_val_509_, 1);
v___x_511_ = lean_apply_1(v_h__2_505_, v_val_510_);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_513_; 
lean_dec(v_h__2_505_);
v_val_512_ = lean_ctor_get(v_val_509_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_val_509_, 1);
v___x_513_ = lean_apply_1(v_h__3_506_, v_val_512_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter(lean_object* v_00_U0001d530_514_, lean_object* v_motive_515_, lean_object* v_x_516_, lean_object* v_h__1_517_, lean_object* v_h__2_518_, lean_object* v_h__3_519_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_val_520_; lean_object* v___x_521_; 
lean_dec(v_h__3_519_);
lean_dec(v_h__2_518_);
v_val_520_ = lean_ctor_get(v_x_516_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_x_516_, 1);
v___x_521_ = lean_apply_1(v_h__1_517_, v_val_520_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; 
lean_dec(v_h__1_517_);
v_val_522_ = lean_ctor_get(v_x_516_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_x_516_, 1);
if (lean_obj_tag(v_val_522_) == 0)
{
lean_object* v_val_523_; lean_object* v___x_524_; 
lean_dec(v_h__3_519_);
v_val_523_ = lean_ctor_get(v_val_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_val_522_, 1);
v___x_524_ = lean_apply_1(v_h__2_518_, v_val_523_);
return v___x_524_;
}
else
{
lean_object* v_val_525_; lean_object* v___x_526_; 
lean_dec(v_h__2_518_);
v_val_525_ = lean_ctor_get(v_val_522_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_val_522_, 1);
v___x_526_ = lean_apply_1(v_h__3_519_, v_val_525_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter___boxed(lean_object* v_00_U0001d530_527_, lean_object* v_motive_528_, lean_object* v_x_529_, lean_object* v_h__1_530_, lean_object* v_h__2_531_, lean_object* v_h__3_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_HyperbolicBasis_middleVector_match__1_splitter(v_00_U0001d530_527_, v_motive_528_, v_x_529_, v_h__1_530_, v_h__2_531_, v_h__3_532_);
lean_dec_ref(v_00_U0001d530_527_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___redArg(lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_h__1_536_, lean_object* v_h__2_537_){
_start:
{
lean_object* v_zero_538_; uint8_t v_isZero_539_; 
v_zero_538_ = lean_unsigned_to_nat(0u);
v_isZero_539_ = lean_nat_dec_eq(v_x_535_, v_zero_538_);
if (v_isZero_539_ == 1)
{
lean_object* v___x_540_; 
lean_dec(v_h__2_537_);
v___x_540_ = lean_apply_1(v_h__1_536_, v_x_534_);
return v___x_540_;
}
else
{
lean_object* v_one_541_; lean_object* v_n_542_; lean_object* v___x_543_; 
lean_dec(v_h__1_536_);
v_one_541_ = lean_unsigned_to_nat(1u);
v_n_542_ = lean_nat_sub(v_x_535_, v_one_541_);
v___x_543_ = lean_apply_2(v_h__2_537_, v_x_534_, v_n_542_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___redArg___boxed(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___redArg(v_x_544_, v_x_545_, v_h__1_546_, v_h__2_547_);
lean_dec(v_x_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter(lean_object* v_motive_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_){
_start:
{
lean_object* v_zero_554_; uint8_t v_isZero_555_; 
v_zero_554_ = lean_unsigned_to_nat(0u);
v_isZero_555_ = lean_nat_dec_eq(v_x_551_, v_zero_554_);
if (v_isZero_555_ == 1)
{
lean_object* v___x_556_; 
lean_dec(v_h__2_553_);
v___x_556_ = lean_apply_1(v_h__1_552_, v_x_550_);
return v___x_556_;
}
else
{
lean_object* v_one_557_; lean_object* v_n_558_; lean_object* v___x_559_; 
lean_dec(v_h__1_552_);
v_one_557_ = lean_unsigned_to_nat(1u);
v_n_558_ = lean_nat_sub(v_x_551_, v_one_557_);
v___x_559_ = lean_apply_2(v_h__2_553_, v_x_550_, v_n_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter___boxed(lean_object* v_motive_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_h__1_563_, lean_object* v_h__2_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_descConv_match__1_splitter(v_motive_560_, v_x_561_, v_x_562_, v_h__1_563_, v_h__2_564_);
lean_dec(v_x_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___redArg(lean_object* v_x_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
lean_object* v_zero_569_; uint8_t v_isZero_570_; 
v_zero_569_ = lean_unsigned_to_nat(0u);
v_isZero_570_ = lean_nat_dec_eq(v_x_566_, v_zero_569_);
if (v_isZero_570_ == 1)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_h__2_568_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_apply_1(v_h__1_567_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_one_573_; lean_object* v_n_574_; lean_object* v___x_575_; 
lean_dec(v_h__1_567_);
v_one_573_ = lean_unsigned_to_nat(1u);
v_n_574_ = lean_nat_sub(v_x_566_, v_one_573_);
v___x_575_ = lean_apply_1(v_h__2_568_, v_n_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___redArg___boxed(lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___redArg(v_x_576_, v_h__1_577_, v_h__2_578_);
lean_dec(v_x_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter(lean_object* v_motive_580_, lean_object* v_x_581_, lean_object* v_h__1_582_, lean_object* v_h__2_583_){
_start:
{
lean_object* v_zero_584_; uint8_t v_isZero_585_; 
v_zero_584_ = lean_unsigned_to_nat(0u);
v_isZero_585_ = lean_nat_dec_eq(v_x_581_, v_zero_584_);
if (v_isZero_585_ == 1)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_h__2_583_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_apply_1(v_h__1_582_, v___x_586_);
return v___x_587_;
}
else
{
lean_object* v_one_588_; lean_object* v_n_589_; lean_object* v___x_590_; 
lean_dec(v_h__1_582_);
v_one_588_ = lean_unsigned_to_nat(1u);
v_n_589_ = lean_nat_sub(v_x_581_, v_one_588_);
v___x_590_ = lean_apply_1(v_h__2_583_, v_n_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter___boxed(lean_object* v_motive_591_, lean_object* v_x_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorMeasures_0__New_Floors_ascConv_match__1_splitter(v_motive_591_, v_x_592_, v_h__1_593_, v_h__2_594_);
lean_dec(v_x_592_);
return v_res_595_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__2(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__0));
v___x_603_ = l_Lean_mkAtom(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__2, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__2_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__2);
v___x_605_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_606_ = lean_array_push(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__4));
v___x_609_ = lean_string_utf8_byte_size(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__6(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_610_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__5, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__5_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__5);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = ((lean_object*)(lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__4));
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___x_610_);
return v___x_613_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__8(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_616_ = lean_box(0);
v___x_617_ = ((lean_object*)(lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__7));
v___x_618_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__6, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__6_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__6);
v___x_619_ = lean_box(2);
v___x_620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_617_);
lean_ctor_set(v___x_620_, 3, v___x_616_);
return v___x_620_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__9(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__8, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__8_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__8);
v___x_622_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__3, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__3_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__3);
v___x_623_ = lean_array_push(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__10(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__9, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__9_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__9);
v___x_625_ = ((lean_object*)(lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__1));
v___x_626_ = lean_box(2);
v___x_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
lean_ctor_set(v___x_627_, 2, v___x_624_);
return v___x_627_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__11(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__10, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__10_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__10);
v___x_629_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_630_ = lean_array_push(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__12(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__11, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__11_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__11);
v___x_632_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__9));
v___x_633_ = lean_box(2);
v___x_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_631_);
return v___x_634_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__13(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__12, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__12_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__12);
v___x_636_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_637_ = lean_array_push(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__14(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__13, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__13_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__13);
v___x_639_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__7));
v___x_640_ = lean_box(2);
v___x_641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
lean_ctor_set(v___x_641_, 2, v___x_638_);
return v___x_641_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__15(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__14, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__14_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__14);
v___x_643_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__5));
v___x_644_ = lean_array_push(v___x_643_, v___x_642_);
return v___x_644_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__16(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__15, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__15_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__15);
v___x_646_ = ((lean_object*)(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1___closed__4));
v___x_647_ = lean_box(2);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v___x_645_);
return v___x_648_;
}
}
static lean_object* _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1(void){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__16, &lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__16_once, _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1___closed__16);
return v___x_649_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorGroups(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Measure_IntegralOperators(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Measure_QuadricDisintegration(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Measure_IntegralOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Measure_QuadricDisintegration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1 = _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1();
lean_mark_persistent(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__1);
lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3 = _init_lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3();
lean_mark_persistent(lp_GRH_New_Floors_map__inclMatrix__eq__floorVolume___auto__3);
lp_GRH_New_Floors_ae__mem__mconv___auto__1 = _init_lp_GRH_New_Floors_ae__mem__mconv___auto__1();
lean_mark_persistent(lp_GRH_New_Floors_ae__mem__mconv___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
