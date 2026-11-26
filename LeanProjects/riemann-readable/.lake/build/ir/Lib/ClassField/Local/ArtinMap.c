// Lean compiler output
// Module: Lib.ClassField.Local.ArtinMap
// Imports: public import Init public meta import Init public import Lib.Adelic.Adeles.IdeleModulus public import Lib.ClassField.LocalDuality.DualityInequality public import Lib.ClassField.Places.TameInertia
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_infinityType___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_infinityType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_infinityType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Mathlib"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__10_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Tauto"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__11_value;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tauto"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__12 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__12_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(118, 213, 161, 2, 73, 184, 31, 228)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value_aux_0),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 222, 98, 232, 116, 132, 69, 249)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value_aux_1),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 83, 25, 243, 21, 136, 46, 247)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value_aux_2),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 227, 116, 33, 242, 140, 204)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13_value;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__14;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__15;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__16_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value_aux_0),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value_aux_1),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value_aux_2),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18_value;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__19;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__26;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__27;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__28;
LEAN_EXPORT lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1;
static const lean_string_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__0 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__0_value;
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value_aux_0),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value_aux_1),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value_aux_2),((lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1 = (const lean_object*)&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1_value;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__2;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__3;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__4;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__5;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__6;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__7;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__8;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__9;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__10;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__11;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__12;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__13;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__14;
static lean_once_cell_t lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15;
LEAN_EXPORT lean_object* lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3;
LEAN_EXPORT lean_object* lp_GRH_New_IsPlaceOver_exists__localArtin__eq___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character___redArg(lean_object* v_00_u03b8_1_){
_start:
{
lean_object* v_fst_2_; 
v_fst_2_ = lean_ctor_get(v_00_u03b8_1_, 0);
lean_inc(v_fst_2_);
return v_fst_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character___redArg___boxed(lean_object* v_00_u03b8_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_AlgHeckeChar_character___redArg(v_00_u03b8_3_);
lean_dec_ref(v_00_u03b8_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character(lean_object* v_K_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_00_u03b8_8_){
_start:
{
lean_object* v_fst_9_; 
v_fst_9_ = lean_ctor_get(v_00_u03b8_8_, 0);
lean_inc(v_fst_9_);
return v_fst_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_character___boxed(lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_00_u03b8_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_AlgHeckeChar_character(v_K_10_, v_inst_11_, v_inst_12_, v_00_u03b8_13_);
lean_dec_ref(v_00_u03b8_13_);
lean_dec_ref(v_inst_11_);
return v_res_14_;
}
}
static lean_object* _init_lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_mathlib_Multiplicative_toAdd___redArg();
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_infinityType___redArg(lean_object* v_00_u03b8_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_snd_18_; lean_object* v___x_19_; lean_object* v_toFun_20_; lean_object* v___x_21_; 
v_snd_18_ = lean_ctor_get(v_00_u03b8_16_, 1);
lean_inc(v_snd_18_);
lean_dec_ref(v_00_u03b8_16_);
v___x_19_ = lean_obj_once(&lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0, &lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0_once, _init_lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0);
v_toFun_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_toFun_20_);
v___x_21_ = lean_apply_2(v_toFun_20_, v_snd_18_, v_a_17_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_infinityType(lean_object* v_K_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_00_u03b8_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_snd_27_; lean_object* v___x_28_; lean_object* v_toFun_29_; lean_object* v___x_30_; 
v_snd_27_ = lean_ctor_get(v_00_u03b8_25_, 1);
lean_inc(v_snd_27_);
lean_dec_ref(v_00_u03b8_25_);
v___x_28_ = lean_obj_once(&lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0, &lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0_once, _init_lp_GRH_New_AlgHeckeChar_infinityType___redArg___closed__0);
v_toFun_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_toFun_29_);
v___x_30_ = lean_apply_2(v_toFun_29_, v_snd_27_, v_a_26_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_AlgHeckeChar_infinityType___boxed(lean_object* v_K_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_00_u03b8_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_AlgHeckeChar_infinityType(v_K_31_, v_inst_32_, v_inst_33_, v_00_u03b8_34_, v_a_35_);
lean_dec_ref(v_inst_32_);
return v_res_36_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__14(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__12));
v___x_66_ = l_Lean_mkAtom(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__15(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__14, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__14_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__14);
v___x_68_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__19(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18));
v___x_81_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__19, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__19_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__19);
v___x_84_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__17));
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__21(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20);
v___x_88_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__15, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__15_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__15);
v___x_89_ = lean_array_push(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__22(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__21, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__21_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__21);
v___x_91_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__13));
v___x_92_ = lean_box(2);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__23(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__22, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__22_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__22);
v___x_95_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__24(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__23, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__23_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__23);
v___x_98_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__9));
v___x_99_ = lean_box(2);
v___x_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__25(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__24, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__24_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__24);
v___x_102_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__26(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__25, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__25_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__25);
v___x_105_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__27(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__26, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__26_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__26);
v___x_109_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_110_ = lean_array_push(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__28(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__27, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__27_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__27);
v___x_112_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4));
v___x_113_ = lean_box(2);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__28, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__28_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__28);
return v___x_115_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__2(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__0));
v___x_123_ = l_Lean_mkAtom(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__3(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__2, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__2_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__2);
v___x_125_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__4(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__20);
v___x_128_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__3, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__3_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__3);
v___x_129_ = lean_array_push(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__5(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18));
v___x_131_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__4, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__4_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__4);
v___x_132_ = lean_array_push(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__6(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18));
v___x_134_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__5, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__5_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__5);
v___x_135_ = lean_array_push(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__7(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18));
v___x_137_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__6, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__6_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__6);
v___x_138_ = lean_array_push(v___x_137_, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__8(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__18));
v___x_140_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__7, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__7_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__7);
v___x_141_ = lean_array_push(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__9(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__8, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__8_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__8);
v___x_143_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__1));
v___x_144_ = lean_box(2);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_142_);
return v___x_145_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__10(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__9, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__9_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__9);
v___x_147_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_148_ = lean_array_push(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__11(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__10, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__10_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__10);
v___x_150_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__9));
v___x_151_ = lean_box(2);
v___x_152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
lean_ctor_set(v___x_152_, 2, v___x_149_);
return v___x_152_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__12(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__11, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__11_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__11);
v___x_154_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_155_ = lean_array_push(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__13(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__12, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__12_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__12);
v___x_157_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__7));
v___x_158_ = lean_box(2);
v___x_159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__14(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__13, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__13_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__13);
v___x_161_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__5));
v___x_162_ = lean_array_push(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__14, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__14_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__14);
v___x_164_ = ((lean_object*)(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1___closed__4));
v___x_165_ = lean_box(2);
v___x_166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
return v___x_166_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15);
return v___x_167_;
}
}
static lean_object* _init_lp_GRH_New_IsPlaceOver_exists__localArtin__eq___auto__1(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15, &lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15_once, _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3___closed__15);
return v___x_168_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Adeles_IdeleModulus(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_LocalDuality_DualityInequality(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_TameInertia(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_Local_ArtinMap(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Adeles_IdeleModulus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_LocalDuality_DualityInequality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Places_TameInertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1 = _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1();
lean_mark_persistent(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__1);
lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3 = _init_lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3();
lean_mark_persistent(lp_GRH_New_IsPlaceOver_localArtin__localNorm___auto__3);
lp_GRH_New_IsPlaceOver_exists__localArtin__eq___auto__1 = _init_lp_GRH_New_IsPlaceOver_exists__localArtin__eq___auto__1();
lean_mark_persistent(lp_GRH_New_IsPlaceOver_exists__localArtin__eq___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
