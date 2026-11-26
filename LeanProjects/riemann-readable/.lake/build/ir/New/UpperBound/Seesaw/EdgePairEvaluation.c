// Lean compiler output
// Module: New.UpperBound.Seesaw.EdgePairEvaluation
// Imports: public import Init public meta import Init public import Lib.Weil.DualPair.TwoEdges public import Lib.Weil.MixedModel.AdaptedSplitting public import Lib.Weil.Periods.ConstantTerm public import New.UpperBound.Objects.Rows
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Function_Embedding_inl___redArg___lam__0(lean_object*);
lean_object* lp_mathlib_Equiv_toEmbedding___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Function_Embedding_trans___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_Embedding_prodMap___redArg(lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_inclMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_kroneckerMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Function_Embedding_inl___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___boxed(lean_object**);
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Data_gradingY___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__11_value;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__13;
static const lean_string_object lp_GRH_New_Data_gradingY___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__14_value;
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__15_value_aux_0),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__15_value_aux_1),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__15_value_aux_2),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__15_value;
static const lean_ctor_object lp_GRH_New_Data_gradingY___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_Data_gradingY___auto__1___closed__16_value;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__17;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__18;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__19;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__20;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_Data_gradingY___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gradingY___auto__1___closed__26;
LEAN_EXPORT lean_object* lp_GRH_New_Data_gradingY___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__0(lean_object* v_val_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2_, 0, v_val_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__1(lean_object* v_toMul_3_, lean_object* v_x1_4_, lean_object* v_x2_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_2(v_toMul_3_, v_x1_4_, v_x2_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__2(lean_object* v_indexEquiv_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_toFun_9_; lean_object* v___x_10_; 
v_toFun_9_ = lean_ctor_get(v_indexEquiv_7_, 0);
lean_inc(v_toFun_9_);
lean_dec_ref(v_indexEquiv_7_);
v___x_10_ = lean_apply_1(v_toFun_9_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_Y_x27_15_, lean_object* v_Z_16_){
_start:
{
lean_object* v___x_17_; lean_object* v_toCommSemiring_18_; lean_object* v___x_19_; lean_object* v_toMul_20_; lean_object* v___x_21_; lean_object* v_toZero_22_; lean_object* v___x_23_; lean_object* v_toRing_24_; lean_object* v___x_25_; lean_object* v_toAddMonoidWithOne_26_; lean_object* v_toOne_27_; lean_object* v_index_28_; lean_object* v_incl_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_47_; 
v___x_17_ = lp_mathlib_Field_toSemifield___redArg(v_inst_13_);
v_toCommSemiring_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref_n(v_toCommSemiring_18_, 2);
lean_dec_ref(v___x_17_);
v___x_19_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_18_);
v_toMul_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_toMul_20_);
lean_dec_ref(v___x_19_);
v___x_21_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_18_);
v_toZero_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_toZero_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_13_);
v_toRing_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_toRing_24_);
lean_dec_ref(v___x_23_);
v___x_25_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_24_);
v_toAddMonoidWithOne_26_ = lean_ctor_get(v___x_25_, 1);
lean_inc_ref(v_toAddMonoidWithOne_26_);
lean_dec_ref(v___x_25_);
v_toOne_27_ = lean_ctor_get(v_toAddMonoidWithOne_26_, 2);
lean_inc(v_toOne_27_);
lean_dec_ref(v_toAddMonoidWithOne_26_);
v_index_28_ = lean_ctor_get(v_Z_16_, 0);
v_incl_29_ = lean_ctor_get(v_Z_16_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_Z_16_);
if (v_isSharedCheck_47_ == 0)
{
v___x_31_ = v_Z_16_;
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_incl_29_);
lean_inc(v_index_28_);
lean_dec(v_Z_16_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_indexEquiv_33_; lean_object* v___f_34_; lean_object* v___f_35_; lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v_indexEquiv_33_ = lean_ctor_get(v_Y_x27_15_, 0);
lean_inc_ref_n(v_indexEquiv_33_, 2);
lean_dec_ref(v_Y_x27_15_);
v___f_34_ = ((lean_object*)(lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__0));
v___f_35_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__1), 3, 1);
lean_closure_set(v___f_35_, 0, v_toMul_20_);
v___f_36_ = ((lean_object*)(lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___closed__1));
v___f_37_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg___lam__2), 2, 1);
lean_closure_set(v___f_37_, 0, v_indexEquiv_33_);
v___f_38_ = lean_alloc_closure((void*)(lp_mathlib_Equiv_toEmbedding___redArg___lam__0), 2, 1);
lean_closure_set(v___f_38_, 0, v_indexEquiv_33_);
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_Function_Embedding_trans___redArg___lam__0), 3, 2);
lean_closure_set(v___f_39_, 0, v___f_36_);
lean_closure_set(v___f_39_, 1, v___f_38_);
v___x_40_ = lp_mathlib_Function_Embedding_prodMap___redArg(v_index_28_, v___f_39_);
v___x_41_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_41_, 0, lean_box(0));
lean_closure_set(v___x_41_, 1, lean_box(0));
lean_closure_set(v___x_41_, 2, lean_box(0));
lean_closure_set(v___x_41_, 3, v___f_37_);
lean_closure_set(v___x_41_, 4, v___f_34_);
v___x_42_ = lean_alloc_closure((void*)(lp_GRH_New_inclMatrix), 9, 7);
lean_closure_set(v___x_42_, 0, lean_box(0));
lean_closure_set(v___x_42_, 1, lean_box(0));
lean_closure_set(v___x_42_, 2, v_inst_14_);
lean_closure_set(v___x_42_, 3, lean_box(0));
lean_closure_set(v___x_42_, 4, v_toZero_22_);
lean_closure_set(v___x_42_, 5, v_toOne_27_);
lean_closure_set(v___x_42_, 6, v___x_41_);
v___x_43_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_kroneckerMap), 12, 10);
lean_closure_set(v___x_43_, 0, lean_box(0));
lean_closure_set(v___x_43_, 1, lean_box(0));
lean_closure_set(v___x_43_, 2, lean_box(0));
lean_closure_set(v___x_43_, 3, lean_box(0));
lean_closure_set(v___x_43_, 4, lean_box(0));
lean_closure_set(v___x_43_, 5, lean_box(0));
lean_closure_set(v___x_43_, 6, lean_box(0));
lean_closure_set(v___x_43_, 7, v___f_35_);
lean_closure_set(v___x_43_, 8, v_incl_29_);
lean_closure_set(v___x_43_, 9, v___x_42_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v___x_43_);
lean_ctor_set(v___x_31_, 0, v___x_40_);
v___x_45_ = v___x_31_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom(lean_object* v_E_48_, lean_object* v_00_u03b9_49_, lean_object* v_00_u03b9_x27_50_, lean_object* v_00_u03b9_x27_x27_51_, lean_object* v_X_x27_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_00_u03b5_63_, lean_object* v_00_u03b5_x27_64_, lean_object* v_00_u03b5_x27_x27_65_, lean_object* v_s_x27_66_, lean_object* v_V_67_, lean_object* v_V_x27_68_, lean_object* v_V_x27_x27_69_, lean_object* v_N_70_, lean_object* v_Y_x27_71_, lean_object* v_w_72_, lean_object* v_Z_73_, lean_object* v_hs_x27_74_, lean_object* v_hw_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_GRH_New_Seesaw_GradeZeroPart_hom___redArg(v_inst_53_, v_inst_58_, v_Y_x27_71_, v_Z_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_GradeZeroPart_hom___boxed(lean_object** _args){
lean_object* v_E_77_ = _args[0];
lean_object* v_00_u03b9_78_ = _args[1];
lean_object* v_00_u03b9_x27_79_ = _args[2];
lean_object* v_00_u03b9_x27_x27_80_ = _args[3];
lean_object* v_X_x27_81_ = _args[4];
lean_object* v_inst_82_ = _args[5];
lean_object* v_inst_83_ = _args[6];
lean_object* v_inst_84_ = _args[7];
lean_object* v_inst_85_ = _args[8];
lean_object* v_inst_86_ = _args[9];
lean_object* v_inst_87_ = _args[10];
lean_object* v_inst_88_ = _args[11];
lean_object* v_inst_89_ = _args[12];
lean_object* v_inst_90_ = _args[13];
lean_object* v_inst_91_ = _args[14];
lean_object* v_00_u03b5_92_ = _args[15];
lean_object* v_00_u03b5_x27_93_ = _args[16];
lean_object* v_00_u03b5_x27_x27_94_ = _args[17];
lean_object* v_s_x27_95_ = _args[18];
lean_object* v_V_96_ = _args[19];
lean_object* v_V_x27_97_ = _args[20];
lean_object* v_V_x27_x27_98_ = _args[21];
lean_object* v_N_99_ = _args[22];
lean_object* v_Y_x27_100_ = _args[23];
lean_object* v_w_101_ = _args[24];
lean_object* v_Z_102_ = _args[25];
lean_object* v_hs_x27_103_ = _args[26];
lean_object* v_hw_104_ = _args[27];
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_GRH_New_Seesaw_GradeZeroPart_hom(v_E_77_, v_00_u03b9_78_, v_00_u03b9_x27_79_, v_00_u03b9_x27_x27_80_, v_X_x27_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_inst_85_, v_inst_86_, v_inst_87_, v_inst_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_00_u03b5_92_, v_00_u03b5_x27_93_, v_00_u03b5_x27_x27_94_, v_s_x27_95_, v_V_96_, v_V_x27_97_, v_V_x27_x27_98_, v_N_99_, v_Y_x27_100_, v_w_101_, v_Z_102_, v_hs_x27_103_, v_hw_104_);
lean_dec_ref(v_w_101_);
lean_dec(v_N_99_);
lean_dec_ref(v_V_x27_x27_98_);
lean_dec_ref(v_V_x27_97_);
lean_dec_ref(v_V_96_);
lean_dec(v_s_x27_95_);
lean_dec_ref(v_00_u03b5_x27_x27_94_);
lean_dec_ref(v_00_u03b5_x27_93_);
lean_dec_ref(v_00_u03b5_92_);
lean_dec_ref(v_inst_91_);
lean_dec(v_inst_90_);
lean_dec_ref(v_inst_89_);
lean_dec(v_inst_88_);
lean_dec(v_inst_86_);
lean_dec_ref(v_inst_85_);
lean_dec(v_inst_84_);
lean_dec_ref(v_inst_83_);
return v_res_105_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__12(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__10));
v___x_133_ = l_Lean_mkAtom(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__13(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__12, &lp_GRH_New_Data_gradingY___auto__1___closed__12_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__12);
v___x_135_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__5));
v___x_136_ = lean_array_push(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__17(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__16));
v___x_148_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__5));
v___x_149_ = lean_array_push(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__18(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__17, &lp_GRH_New_Data_gradingY___auto__1___closed__17_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__17);
v___x_151_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__15));
v___x_152_ = lean_box(2);
v___x_153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_150_);
return v___x_153_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__19(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__18, &lp_GRH_New_Data_gradingY___auto__1___closed__18_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__18);
v___x_155_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__13, &lp_GRH_New_Data_gradingY___auto__1___closed__13_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__13);
v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__20(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__19, &lp_GRH_New_Data_gradingY___auto__1___closed__19_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__19);
v___x_158_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__11));
v___x_159_ = lean_box(2);
v___x_160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_157_);
return v___x_160_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__21(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__20, &lp_GRH_New_Data_gradingY___auto__1___closed__20_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__20);
v___x_162_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__5));
v___x_163_ = lean_array_push(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__22(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__21, &lp_GRH_New_Data_gradingY___auto__1___closed__21_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__21);
v___x_165_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__9));
v___x_166_ = lean_box(2);
v___x_167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_164_);
return v___x_167_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__23(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__22, &lp_GRH_New_Data_gradingY___auto__1___closed__22_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__22);
v___x_169_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__5));
v___x_170_ = lean_array_push(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__24(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__23, &lp_GRH_New_Data_gradingY___auto__1___closed__23_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__23);
v___x_172_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__7));
v___x_173_ = lean_box(2);
v___x_174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_171_);
return v___x_174_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__25(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__24, &lp_GRH_New_Data_gradingY___auto__1___closed__24_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__24);
v___x_176_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__5));
v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1___closed__26(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__25, &lp_GRH_New_Data_gradingY___auto__1___closed__25_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__25);
v___x_179_ = ((lean_object*)(lp_GRH_New_Data_gradingY___auto__1___closed__4));
v___x_180_ = lean_box(2);
v___x_181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_178_);
return v___x_181_;
}
}
static lean_object* _init_lp_GRH_New_Data_gradingY___auto__1(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&lp_GRH_New_Data_gradingY___auto__1___closed__26, &lp_GRH_New_Data_gradingY___auto__1___closed__26_once, _init_lp_GRH_New_Data_gradingY___auto__1___closed__26);
return v___x_182_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_TwoEdges(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_MixedModel_AdaptedSplitting(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_ConstantTerm(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Seesaw_EdgePairEvaluation(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_DualPair_TwoEdges(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_MixedModel_AdaptedSplitting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Periods_ConstantTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Rows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Data_gradingY___auto__1 = _init_lp_GRH_New_Data_gradingY___auto__1();
lean_mark_persistent(lp_GRH_New_Data_gradingY___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
