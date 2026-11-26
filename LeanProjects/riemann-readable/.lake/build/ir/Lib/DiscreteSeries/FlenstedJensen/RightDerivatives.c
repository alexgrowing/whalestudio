// Lean compiler output
// Module: Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Haar.TotalMass public import Lib.DiscreteSeries.Rigidity.RepresentationsAndCasimirs public import Lib.General.Analysis.HolomorphicIntegrals
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
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lp_mathlib_SMulMemClass_subtype___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__0 = (const lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_funLeft___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__0_value)} };
static const lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__1 = (const lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SMulMemClass_subtype___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__2 = (const lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__2_value;
static const lean_closure_object lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_comp___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__2_value),((lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__1_value)} };
static const lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__3 = (const lean_object*)&lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__3_value;
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Mathlib"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__10_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__11_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunProp"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__12 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__12_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funPropTacStx"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__13 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__13_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(118, 213, 161, 2, 73, 184, 31, 228)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value_aux_0),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(210, 10, 180, 159, 248, 97, 218, 144)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value_aux_1),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 118, 4, 116, 28, 199, 219)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value_aux_2),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(146, 162, 46, 139, 110, 137, 217, 136)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14_value;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fun_prop"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__15 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__15_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__16;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__17;
static const lean_string_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__18 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__18_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value_aux_0),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value_aux_1),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value_aux_2),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19_value;
static const lean_ctor_object lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__9_value),((lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5_value)}};
static const lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__20 = (const lean_object*)&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__20_value;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__26;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__27;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__28;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__29;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__30;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__31;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_smear___auto__1;
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_smoothMatrixFunctions___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions(lean_object* v_n_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_E_8_, lean_object* v_inst_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions___boxed(lean_object* v_n_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_smoothMatrixFunctions(v_n_12_, v_inst_13_, v_inst_14_, v_E_15_, v_inst_16_, v_inst_17_);
lean_dec(v_inst_17_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_14_);
lean_dec(v_inst_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___lam__0(lean_object* v_g_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_val_22_; lean_object* v___x_23_; 
v_val_22_ = lean_ctor_get(v_g_19_, 0);
lean_inc(v_val_22_);
lean_dec_ref(v_g_19_);
v___x_23_ = lean_apply_2(v_val_22_, v___y_20_, v___y_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg(){
_start:
{
lean_object* v___f_32_; 
v___f_32_ = ((lean_object*)(lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__3));
return v___f_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_smoothMatrixFunctions_restrictU___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU(lean_object* v_n_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_00_u03b5_38_, lean_object* v_E_39_, lean_object* v_inst_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v___f_42_; 
v___f_42_ = ((lean_object*)(lp_GRH_New_smoothMatrixFunctions_restrictU___redArg___closed__3));
return v___f_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothMatrixFunctions_restrictU___boxed(lean_object* v_n_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_00_u03b5_46_, lean_object* v_E_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_GRH_New_smoothMatrixFunctions_restrictU(v_n_43_, v_inst_44_, v_inst_45_, v_00_u03b5_46_, v_E_47_, v_inst_48_, v_inst_49_);
lean_dec(v_inst_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_00_u03b5_46_);
lean_dec_ref(v_inst_45_);
lean_dec(v_inst_44_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU___redArg(){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU___redArg___boxed(lean_object* v___dummy_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_GRH_New_SmoothU___redArg();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU(lean_object* v_n_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_00_u03b5_58_, lean_object* v_E_59_, lean_object* v_inst_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SmoothU___boxed(lean_object* v_n_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_00_u03b5_66_, lean_object* v_E_67_, lean_object* v_inst_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_GRH_New_SmoothU(v_n_63_, v_inst_64_, v_inst_65_, v_00_u03b5_66_, v_E_67_, v_inst_68_, v_inst_69_);
lean_dec(v_inst_69_);
lean_dec_ref(v_inst_68_);
lean_dec_ref(v_00_u03b5_66_);
lean_dec_ref(v_inst_65_);
lean_dec(v_inst_64_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps___redArg(){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps___redArg___boxed(lean_object* v___dummy_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_GRH_New_DiscreteSeries_Bumps___redArg();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps(lean_object* v_n_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_00_u03b5_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_Bumps___boxed(lean_object* v_n_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_00_u03b5_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lp_GRH_New_DiscreteSeries_Bumps(v_n_80_, v_inst_81_, v_inst_82_, v_00_u03b5_83_);
lean_dec_ref(v_00_u03b5_83_);
lean_dec_ref(v_inst_82_);
lean_dec(v_inst_81_);
return v_res_84_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__16(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__15));
v___x_116_ = l_Lean_mkAtom(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__17(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__16, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__16_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__16);
v___x_118_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5));
v___x_119_ = lean_array_push(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__21(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__20));
v___x_131_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5));
v___x_132_ = lean_array_push(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__22(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__21, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__21_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__21);
v___x_134_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__19));
v___x_135_ = lean_box(2);
v___x_136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__23(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__22, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__22_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__22);
v___x_138_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__17, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__17_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__17);
v___x_139_ = lean_array_push(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__24(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__20));
v___x_141_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__23, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__23_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__23);
v___x_142_ = lean_array_push(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__25(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__20));
v___x_144_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__24, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__24_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__24);
v___x_145_ = lean_array_push(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__26(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__25, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__25_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__25);
v___x_147_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__14));
v___x_148_ = lean_box(2);
v___x_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_146_);
return v___x_149_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__27(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__26, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__26_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__26);
v___x_151_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5));
v___x_152_ = lean_array_push(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__28(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_153_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__27, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__27_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__27);
v___x_154_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__9));
v___x_155_ = lean_box(2);
v___x_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
lean_ctor_set(v___x_156_, 2, v___x_153_);
return v___x_156_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__29(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__28, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__28_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__28);
v___x_158_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__30(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__29, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__29_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__29);
v___x_161_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__7));
v___x_162_ = lean_box(2);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__31(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__30, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__30_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__30);
v___x_165_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__5));
v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__31, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__31_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__31);
v___x_168_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__4));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32);
return v___x_171_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_smear___auto__1(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32, &lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32_once, _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1___closed__32);
return v___x_172_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Haar_TotalMass(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Rigidity_RepresentationsAndCasimirs(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_RightDerivatives(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Haar_TotalMass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Rigidity_RepresentationsAndCasimirs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1 = _init_lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1();
lean_mark_persistent(lp_GRH_New_DiscreteSeries_integrable__bump__inv__smul___auto__1);
lp_GRH_New_DiscreteSeries_smear___auto__1 = _init_lp_GRH_New_DiscreteSeries_smear___auto__1();
lean_mark_persistent(lp_GRH_New_DiscreteSeries_smear___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
