// Lean compiler output
// Module: Lib.Weil.MixedModel.IsotropicSplitting
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.Eigenvalues public import Lib.Weil.Construction.AdelicRepresentation
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toCols_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toCols_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__1;
static lean_once_cell_t lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_hyperbolicSigns___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_hyperbolicSigns___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_hyperbolicSigns___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_hyperbolicSigns___redArg___closed__0 = (const lean_object*)&lp_GRH_New_hyperbolicSigns___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_hyperbolicSigns___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_hyperbolicSigns___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_hyperbolicSigns___redArg___closed__1 = (const lean_object*)&lp_GRH_New_hyperbolicSigns___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns(lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__13;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__14_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value_aux_0),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value_aux_1),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value_aux_2),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__18;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__19;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__20;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__21;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__22 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__22_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__24;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__25 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__25_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value_aux_0),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value_aux_1),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value_aux_2),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__27;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Function.Injective"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__28 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__28_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__30;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__31 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__31_value;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__32 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__32_value;
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__33_value_aux_0),((lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 162, 25, 76, 92, 227, 14, 201)}};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__33 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__33_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__34;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__35;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__36;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__37;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__38;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__39;
static const lean_string_object lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__40 = (const lean_object*)&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__40_value;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__41;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__42;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__43;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__44;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__45;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__46;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__47;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__48;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__49;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__50;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__51;
static lean_once_cell_t lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__52;
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingOfGram___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingOfGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingOfGram___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_symm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_symm___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0, &lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0_once, _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0);
v___x_4_ = lean_int_neg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__1, &lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__1_once, _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__1);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0(lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__2, &lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__2_once, _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__2);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__0___boxed(lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_GRH_New_hyperbolicSigns___redArg___lam__0(v___y_9_);
lean_dec(v___y_9_);
return v_res_10_;
}
}
static lean_object* _init_lp_GRH_New_hyperbolicSigns___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0, &lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0_once, _init_lp_GRH_New_hyperbolicSigns___redArg___lam__0___closed__0);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__1(lean_object* v_x_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&lp_GRH_New_hyperbolicSigns___redArg___lam__1___closed__0, &lp_GRH_New_hyperbolicSigns___redArg___lam__1___closed__0_once, _init_lp_GRH_New_hyperbolicSigns___redArg___lam__1___closed__0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg___lam__1___boxed(lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_hyperbolicSigns___redArg___lam__1(v_x_15_);
lean_dec(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns___redArg(lean_object* v_a_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v___f_20_ = ((lean_object*)(lp_GRH_New_hyperbolicSigns___redArg___closed__0));
v___f_21_ = ((lean_object*)(lp_GRH_New_hyperbolicSigns___redArg___closed__1));
v___x_22_ = l_Sum_elim___redArg(v___f_21_, v___f_20_, v_a_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperbolicSigns(lean_object* v_p_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v___f_25_ = ((lean_object*)(lp_GRH_New_hyperbolicSigns___redArg___closed__0));
v___f_26_ = ((lean_object*)(lp_GRH_New_hyperbolicSigns___redArg___closed__1));
v___x_27_ = l_Sum_elim___redArg(v___f_26_, v___f_25_, v_a_24_);
return v___x_27_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__12(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__10));
v___x_55_ = l_Lean_mkAtom(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__13(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__12, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__12_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__12);
v___x_57_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16));
v___x_70_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_71_ = lean_array_push(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__18(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17);
v___x_73_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__15));
v___x_74_ = lean_box(2);
v___x_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__19(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__18, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__18_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__18);
v___x_77_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__13, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__13_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__13);
v___x_78_ = lean_array_push(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__20(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16));
v___x_80_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__19, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__19_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__19);
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__21(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16));
v___x_83_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__20, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__20_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__20);
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__23(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__22));
v___x_87_ = l_Lean_mkAtom(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__24(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__23, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__23_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__23);
v___x_89_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__27(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16));
v___x_98_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__17);
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__29(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__28));
v___x_102_ = lean_string_utf8_byte_size(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__30(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__29, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__29_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__29);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__28));
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
return v___x_106_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__34(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = lean_box(0);
v___x_113_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__33));
v___x_114_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__30, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__30_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__30);
v___x_115_ = lean_box(2);
v___x_116_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_113_);
lean_ctor_set(v___x_116_, 3, v___x_112_);
return v___x_116_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__35(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__34, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__34_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__34);
v___x_118_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__27, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__27_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__27);
v___x_119_ = lean_array_push(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__36(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__35, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__35_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__35);
v___x_121_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__26));
v___x_122_ = lean_box(2);
v___x_123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__37(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__36, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__36_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__36);
v___x_125_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__38(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__37, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__37_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__37);
v___x_128_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9));
v___x_129_ = lean_box(2);
v___x_130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__39(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__38, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__38_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__38);
v___x_132_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__24, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__24_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__24);
v___x_133_ = lean_array_push(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__41(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__40));
v___x_136_ = l_Lean_mkAtom(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__42(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__41, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__41_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__41);
v___x_138_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__39, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__39_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__39);
v___x_139_ = lean_array_push(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__43(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__42, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__42_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__42);
v___x_141_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9));
v___x_142_ = lean_box(2);
v___x_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_140_);
return v___x_143_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__44(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__43, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__43_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__43);
v___x_145_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__21, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__21_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__21);
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__45(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__16));
v___x_148_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__44, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__44_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__44);
v___x_149_ = lean_array_push(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__46(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__45, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__45_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__45);
v___x_151_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__11));
v___x_152_ = lean_box(2);
v___x_153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_150_);
return v___x_153_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__47(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__46, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__46_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__46);
v___x_155_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__48(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__47, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__47_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__47);
v___x_158_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__9));
v___x_159_ = lean_box(2);
v___x_160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_157_);
return v___x_160_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__49(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__48, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__48_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__48);
v___x_162_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_163_ = lean_array_push(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__50(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__49, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__49_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__49);
v___x_165_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__7));
v___x_166_ = lean_box(2);
v___x_167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_164_);
return v___x_167_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__51(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__50, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__50_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__50);
v___x_169_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__5));
v___x_170_ = lean_array_push(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__52(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__51, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__51_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__51);
v___x_172_ = ((lean_object*)(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__4));
v___x_173_ = lean_box(2);
v___x_174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_171_);
return v___x_174_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__52, &lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__52_once, _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1___closed__52);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingOfGram___redArg(lean_object* v_M_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v_M_176_);
v___x_177_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toCols_u2081), 7, 5);
lean_closure_set(v___x_177_, 0, lean_box(0));
lean_closure_set(v___x_177_, 1, lean_box(0));
lean_closure_set(v___x_177_, 2, lean_box(0));
lean_closure_set(v___x_177_, 3, lean_box(0));
lean_closure_set(v___x_177_, 4, v_M_176_);
lean_inc_ref(v___x_177_);
v___x_178_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toCols_u2082), 7, 5);
lean_closure_set(v___x_178_, 0, lean_box(0));
lean_closure_set(v___x_178_, 1, lean_box(0));
lean_closure_set(v___x_178_, 2, lean_box(0));
lean_closure_set(v___x_178_, 3, lean_box(0));
lean_closure_set(v___x_178_, 4, v___x_177_);
v___x_179_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toCols_u2081), 7, 5);
lean_closure_set(v___x_179_, 0, lean_box(0));
lean_closure_set(v___x_179_, 1, lean_box(0));
lean_closure_set(v___x_179_, 2, lean_box(0));
lean_closure_set(v___x_179_, 3, lean_box(0));
lean_closure_set(v___x_179_, 4, v___x_177_);
v___x_180_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toCols_u2082), 7, 5);
lean_closure_set(v___x_180_, 0, lean_box(0));
lean_closure_set(v___x_180_, 1, lean_box(0));
lean_closure_set(v___x_180_, 2, lean_box(0));
lean_closure_set(v___x_180_, 3, lean_box(0));
lean_closure_set(v___x_180_, 4, v_M_176_);
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_178_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingOfGram(lean_object* v_E_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_n_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_s_188_, lean_object* v_V_189_, lean_object* v_inst_190_, lean_object* v_n_u2080_191_, lean_object* v_p_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_s_u2080_197_, lean_object* v_V_u2080_198_, lean_object* v_M_199_, lean_object* v_h__gram_200_, lean_object* v_h__card_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lp_GRH_New_Exchange_splittingOfGram___redArg(v_M_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingOfGram___boxed(lean_object** _args){
lean_object* v_E_203_ = _args[0];
lean_object* v_inst_204_ = _args[1];
lean_object* v_inst_205_ = _args[2];
lean_object* v_n_206_ = _args[3];
lean_object* v_inst_207_ = _args[4];
lean_object* v_inst_208_ = _args[5];
lean_object* v_s_209_ = _args[6];
lean_object* v_V_210_ = _args[7];
lean_object* v_inst_211_ = _args[8];
lean_object* v_n_u2080_212_ = _args[9];
lean_object* v_p_213_ = _args[10];
lean_object* v_inst_214_ = _args[11];
lean_object* v_inst_215_ = _args[12];
lean_object* v_inst_216_ = _args[13];
lean_object* v_inst_217_ = _args[14];
lean_object* v_s_u2080_218_ = _args[15];
lean_object* v_V_u2080_219_ = _args[16];
lean_object* v_M_220_ = _args[17];
lean_object* v_h__gram_221_ = _args[18];
lean_object* v_h__card_222_ = _args[19];
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_GRH_New_Exchange_splittingOfGram(v_E_203_, v_inst_204_, v_inst_205_, v_n_206_, v_inst_207_, v_inst_208_, v_s_209_, v_V_210_, v_inst_211_, v_n_u2080_212_, v_p_213_, v_inst_214_, v_inst_215_, v_inst_216_, v_inst_217_, v_s_u2080_218_, v_V_u2080_219_, v_M_220_, v_h__gram_221_, v_h__card_222_);
lean_dec_ref(v_V_u2080_219_);
lean_dec_ref(v_s_u2080_218_);
lean_dec_ref(v_inst_217_);
lean_dec(v_inst_216_);
lean_dec_ref(v_inst_215_);
lean_dec(v_inst_214_);
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_V_210_);
lean_dec_ref(v_s_209_);
lean_dec_ref(v_inst_208_);
lean_dec(v_inst_207_);
lean_dec_ref(v_inst_205_);
lean_dec_ref(v_inst_204_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_symm___redArg(lean_object* v_D_224_){
_start:
{
lean_object* v_k_225_; lean_object* v_l_226_; lean_object* v_i_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_k_225_ = lean_ctor_get(v_D_224_, 0);
v_l_226_ = lean_ctor_get(v_D_224_, 1);
v_i_227_ = lean_ctor_get(v_D_224_, 2);
v_isSharedCheck_234_ = !lean_is_exclusive(v_D_224_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v_D_224_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_i_227_);
lean_inc(v_l_226_);
lean_inc(v_k_225_);
lean_dec(v_D_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v_k_225_);
lean_ctor_set(v___x_229_, 0, v_l_226_);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_l_226_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_k_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_i_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_symm(lean_object* v_E_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_n_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_s_241_, lean_object* v_V_242_, lean_object* v_n_u2080_243_, lean_object* v_p_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_s_u2080_249_, lean_object* v_V_u2080_250_, lean_object* v_D_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lp_GRH_New_Space_Splitting_symm___redArg(v_D_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_symm___boxed(lean_object** _args){
lean_object* v_E_253_ = _args[0];
lean_object* v_inst_254_ = _args[1];
lean_object* v_inst_255_ = _args[2];
lean_object* v_n_256_ = _args[3];
lean_object* v_inst_257_ = _args[4];
lean_object* v_inst_258_ = _args[5];
lean_object* v_s_259_ = _args[6];
lean_object* v_V_260_ = _args[7];
lean_object* v_n_u2080_261_ = _args[8];
lean_object* v_p_262_ = _args[9];
lean_object* v_inst_263_ = _args[10];
lean_object* v_inst_264_ = _args[11];
lean_object* v_inst_265_ = _args[12];
lean_object* v_inst_266_ = _args[13];
lean_object* v_s_u2080_267_ = _args[14];
lean_object* v_V_u2080_268_ = _args[15];
lean_object* v_D_269_ = _args[16];
_start:
{
lean_object* v_res_270_; 
v_res_270_ = lp_GRH_New_Space_Splitting_symm(v_E_253_, v_inst_254_, v_inst_255_, v_n_256_, v_inst_257_, v_inst_258_, v_s_259_, v_V_260_, v_n_u2080_261_, v_p_262_, v_inst_263_, v_inst_264_, v_inst_265_, v_inst_266_, v_s_u2080_267_, v_V_u2080_268_, v_D_269_);
lean_dec_ref(v_V_u2080_268_);
lean_dec_ref(v_s_u2080_267_);
lean_dec_ref(v_inst_266_);
lean_dec(v_inst_265_);
lean_dec_ref(v_inst_264_);
lean_dec(v_inst_263_);
lean_dec_ref(v_V_260_);
lean_dec_ref(v_s_259_);
lean_dec_ref(v_inst_258_);
lean_dec(v_inst_257_);
lean_dec_ref(v_inst_255_);
lean_dec_ref(v_inst_254_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__0(lean_object* v_i_271_, lean_object* v___y_272_, lean_object* v_j_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_apply_2(v_i_271_, v_j_273_, v___y_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__1(lean_object* v_i_275_, lean_object* v___y_276_, lean_object* v_j_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_apply_2(v_i_275_, v___y_276_, v_j_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__2(lean_object* v_i_279_, lean_object* v_i_280_, lean_object* v_inst_281_, lean_object* v_toMul_282_, lean_object* v_toAddCommMonoid_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_286_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_286_, 0, v_i_279_);
lean_closure_set(v___f_286_, 1, v___y_285_);
v___f_287_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__1), 3, 2);
lean_closure_set(v___f_287_, 0, v_i_280_);
lean_closure_set(v___f_287_, 1, v___y_284_);
v___x_288_ = lp_mathlib_dotProduct___redArg(v_inst_281_, v_toMul_282_, v_toAddCommMonoid_283_, v___f_287_, v___f_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__2___boxed(lean_object* v_i_289_, lean_object* v_i_290_, lean_object* v_inst_291_, lean_object* v_toMul_292_, lean_object* v_toAddCommMonoid_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = lp_GRH_New_Space_Splitting_comp___redArg___lam__2(v_i_289_, v_i_290_, v_inst_291_, v_toMul_292_, v_toAddCommMonoid_293_, v___y_294_, v___y_295_);
lean_dec_ref(v_toAddCommMonoid_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__3(lean_object* v_l_297_, lean_object* v___y_298_, lean_object* v_j_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_apply_2(v_l_297_, v_j_299_, v___y_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__5(lean_object* v_l_301_, lean_object* v_i_302_, lean_object* v_inst_303_, lean_object* v_toMul_304_, lean_object* v_toAddCommMonoid_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v___x_310_; 
v___f_308_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__3), 3, 2);
lean_closure_set(v___f_308_, 0, v_l_301_);
lean_closure_set(v___f_308_, 1, v___y_307_);
v___f_309_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__1), 3, 2);
lean_closure_set(v___f_309_, 0, v_i_302_);
lean_closure_set(v___f_309_, 1, v___y_306_);
v___x_310_ = lp_mathlib_dotProduct___redArg(v_inst_303_, v_toMul_304_, v_toAddCommMonoid_305_, v___f_309_, v___f_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__5___boxed(lean_object* v_l_311_, lean_object* v_i_312_, lean_object* v_inst_313_, lean_object* v_toMul_314_, lean_object* v_toAddCommMonoid_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = lp_GRH_New_Space_Splitting_comp___redArg___lam__5(v_l_311_, v_i_312_, v_inst_313_, v_toMul_314_, v_toAddCommMonoid_315_, v___y_316_, v___y_317_);
lean_dec_ref(v_toAddCommMonoid_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__4(lean_object* v_k_319_, lean_object* v___y_320_, lean_object* v_j_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_apply_2(v_k_319_, v_j_321_, v___y_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__7(lean_object* v_k_323_, lean_object* v_i_324_, lean_object* v_inst_325_, lean_object* v_toMul_326_, lean_object* v_toAddCommMonoid_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___x_332_; 
v___f_330_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__4), 3, 2);
lean_closure_set(v___f_330_, 0, v_k_323_);
lean_closure_set(v___f_330_, 1, v___y_329_);
v___f_331_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__1), 3, 2);
lean_closure_set(v___f_331_, 0, v_i_324_);
lean_closure_set(v___f_331_, 1, v___y_328_);
v___x_332_ = lp_mathlib_dotProduct___redArg(v_inst_325_, v_toMul_326_, v_toAddCommMonoid_327_, v___f_331_, v___f_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___lam__7___boxed(lean_object* v_k_333_, lean_object* v_i_334_, lean_object* v_inst_335_, lean_object* v_toMul_336_, lean_object* v_toAddCommMonoid_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = lp_GRH_New_Space_Splitting_comp___redArg___lam__7(v_k_333_, v_i_334_, v_inst_335_, v_toMul_336_, v_toAddCommMonoid_337_, v___y_338_, v___y_339_);
lean_dec_ref(v_toAddCommMonoid_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg(lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_D_343_, lean_object* v_D_x27_344_){
_start:
{
lean_object* v___x_345_; lean_object* v_toCommSemiring_346_; lean_object* v___x_347_; lean_object* v_toMul_348_; lean_object* v_toAddCommMonoid_349_; lean_object* v_k_350_; lean_object* v_l_351_; lean_object* v_i_352_; lean_object* v_k_353_; lean_object* v_l_354_; lean_object* v_i_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_367_; 
v___x_345_ = lp_mathlib_Field_toSemifield___redArg(v_inst_341_);
v_toCommSemiring_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref_n(v_toCommSemiring_346_, 2);
lean_dec_ref(v___x_345_);
v___x_347_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_346_);
v_toMul_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_toMul_348_);
lean_dec_ref(v___x_347_);
v_toAddCommMonoid_349_ = lean_ctor_get(v_toCommSemiring_346_, 0);
lean_inc_ref(v_toAddCommMonoid_349_);
lean_dec_ref(v_toCommSemiring_346_);
v_k_350_ = lean_ctor_get(v_D_343_, 0);
lean_inc(v_k_350_);
v_l_351_ = lean_ctor_get(v_D_343_, 1);
lean_inc(v_l_351_);
v_i_352_ = lean_ctor_get(v_D_343_, 2);
lean_inc(v_i_352_);
lean_dec_ref(v_D_343_);
v_k_353_ = lean_ctor_get(v_D_x27_344_, 0);
v_l_354_ = lean_ctor_get(v_D_x27_344_, 1);
v_i_355_ = lean_ctor_get(v_D_x27_344_, 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_D_x27_344_);
if (v_isSharedCheck_367_ == 0)
{
v___x_357_ = v_D_x27_344_;
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_i_355_);
lean_inc(v_l_354_);
lean_inc(v_k_353_);
lean_dec(v_D_x27_344_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
lean_inc_ref_n(v_toAddCommMonoid_349_, 2);
lean_inc_n(v_toMul_348_, 2);
lean_inc_n(v_inst_342_, 2);
lean_inc_n(v_i_352_, 2);
v___f_359_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_359_, 0, v_i_355_);
lean_closure_set(v___f_359_, 1, v_i_352_);
lean_closure_set(v___f_359_, 2, v_inst_342_);
lean_closure_set(v___f_359_, 3, v_toMul_348_);
lean_closure_set(v___f_359_, 4, v_toAddCommMonoid_349_);
v___f_360_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_360_, 0, v_l_354_);
lean_closure_set(v___f_360_, 1, v_i_352_);
lean_closure_set(v___f_360_, 2, v_inst_342_);
lean_closure_set(v___f_360_, 3, v_toMul_348_);
lean_closure_set(v___f_360_, 4, v_toAddCommMonoid_349_);
v___f_361_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_comp___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_361_, 0, v_k_353_);
lean_closure_set(v___f_361_, 1, v_i_352_);
lean_closure_set(v___f_361_, 2, v_inst_342_);
lean_closure_set(v___f_361_, 3, v_toMul_348_);
lean_closure_set(v___f_361_, 4, v_toAddCommMonoid_349_);
v___x_362_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromCols), 8, 6);
lean_closure_set(v___x_362_, 0, lean_box(0));
lean_closure_set(v___x_362_, 1, lean_box(0));
lean_closure_set(v___x_362_, 2, lean_box(0));
lean_closure_set(v___x_362_, 3, lean_box(0));
lean_closure_set(v___x_362_, 4, v_k_350_);
lean_closure_set(v___x_362_, 5, v___f_361_);
v___x_363_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromCols), 8, 6);
lean_closure_set(v___x_363_, 0, lean_box(0));
lean_closure_set(v___x_363_, 1, lean_box(0));
lean_closure_set(v___x_363_, 2, lean_box(0));
lean_closure_set(v___x_363_, 3, lean_box(0));
lean_closure_set(v___x_363_, 4, v_l_351_);
lean_closure_set(v___x_363_, 5, v___f_360_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 2, v___f_359_);
lean_ctor_set(v___x_357_, 1, v___x_363_);
lean_ctor_set(v___x_357_, 0, v___x_362_);
v___x_365_ = v___x_357_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v___f_359_);
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
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___redArg___boxed(lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_D_370_, lean_object* v_D_x27_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = lp_GRH_New_Space_Splitting_comp___redArg(v_inst_368_, v_inst_369_, v_D_370_, v_D_x27_371_);
lean_dec_ref(v_inst_368_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp(lean_object* v_E_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_n_376_, lean_object* v_n_u2081_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_s_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_s_u2081_383_, lean_object* v_V_u2081_384_, lean_object* v_V_385_, lean_object* v_n_u2080_386_, lean_object* v_p_387_, lean_object* v_q_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_s_u2080_393_, lean_object* v_V_u2080_394_, lean_object* v_D_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_D_x27_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lp_GRH_New_Space_Splitting_comp___redArg(v_inst_374_, v_inst_389_, v_D_395_, v_D_x27_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_comp___boxed(lean_object** _args){
lean_object* v_E_400_ = _args[0];
lean_object* v_inst_401_ = _args[1];
lean_object* v_inst_402_ = _args[2];
lean_object* v_n_403_ = _args[3];
lean_object* v_n_u2081_404_ = _args[4];
lean_object* v_inst_405_ = _args[5];
lean_object* v_inst_406_ = _args[6];
lean_object* v_s_407_ = _args[7];
lean_object* v_inst_408_ = _args[8];
lean_object* v_inst_409_ = _args[9];
lean_object* v_s_u2081_410_ = _args[10];
lean_object* v_V_u2081_411_ = _args[11];
lean_object* v_V_412_ = _args[12];
lean_object* v_n_u2080_413_ = _args[13];
lean_object* v_p_414_ = _args[14];
lean_object* v_q_415_ = _args[15];
lean_object* v_inst_416_ = _args[16];
lean_object* v_inst_417_ = _args[17];
lean_object* v_inst_418_ = _args[18];
lean_object* v_inst_419_ = _args[19];
lean_object* v_s_u2080_420_ = _args[20];
lean_object* v_V_u2080_421_ = _args[21];
lean_object* v_D_422_ = _args[22];
lean_object* v_inst_423_ = _args[23];
lean_object* v_inst_424_ = _args[24];
lean_object* v_D_x27_425_ = _args[25];
_start:
{
lean_object* v_res_426_; 
v_res_426_ = lp_GRH_New_Space_Splitting_comp(v_E_400_, v_inst_401_, v_inst_402_, v_n_403_, v_n_u2081_404_, v_inst_405_, v_inst_406_, v_s_407_, v_inst_408_, v_inst_409_, v_s_u2081_410_, v_V_u2081_411_, v_V_412_, v_n_u2080_413_, v_p_414_, v_q_415_, v_inst_416_, v_inst_417_, v_inst_418_, v_inst_419_, v_s_u2080_420_, v_V_u2080_421_, v_D_422_, v_inst_423_, v_inst_424_, v_D_x27_425_);
lean_dec_ref(v_inst_424_);
lean_dec(v_inst_423_);
lean_dec_ref(v_V_u2080_421_);
lean_dec_ref(v_s_u2080_420_);
lean_dec_ref(v_inst_419_);
lean_dec(v_inst_418_);
lean_dec_ref(v_inst_417_);
lean_dec_ref(v_V_412_);
lean_dec_ref(v_V_u2081_411_);
lean_dec_ref(v_s_u2081_410_);
lean_dec_ref(v_inst_409_);
lean_dec(v_inst_408_);
lean_dec_ref(v_s_407_);
lean_dec_ref(v_inst_406_);
lean_dec(v_inst_405_);
lean_dec_ref(v_inst_402_);
lean_dec_ref(v_inst_401_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic___redArg(){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_box(0);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic___redArg___boxed(lean_object* v___dummy_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = lp_GRH_New_Space_Splitting_siegelParabolic___redArg();
return v_res_430_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic(lean_object* v_E_431_, lean_object* v_p_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_n_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_s_440_, lean_object* v_V_441_, lean_object* v_D_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_box(0);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_siegelParabolic___boxed(lean_object* v_E_444_, lean_object* v_p_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_n_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_s_453_, lean_object* v_V_454_, lean_object* v_D_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = lp_GRH_New_Space_Splitting_siegelParabolic(v_E_444_, v_p_445_, v_inst_446_, v_inst_447_, v_inst_448_, v_inst_449_, v_n_450_, v_inst_451_, v_inst_452_, v_s_453_, v_V_454_, v_D_455_);
lean_dec_ref(v_D_455_);
lean_dec_ref(v_V_454_);
lean_dec_ref(v_s_453_);
lean_dec_ref(v_inst_452_);
lean_dec(v_inst_451_);
lean_dec_ref(v_inst_449_);
lean_dec(v_inst_448_);
lean_dec_ref(v_inst_447_);
lean_dec_ref(v_inst_446_);
return v_res_456_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_AdelicRepresentation(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_MixedModel_IsotropicSplitting(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Construction_AdelicRepresentation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1 = _init_lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1();
lean_mark_persistent(lp_GRH_New_Exchange_IsOrthoIntegral_of__eq__submatrix__mul___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
