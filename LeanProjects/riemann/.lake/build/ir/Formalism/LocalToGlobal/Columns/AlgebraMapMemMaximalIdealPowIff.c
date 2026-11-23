// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.StatementLat public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv___lam__1(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_plEquiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_plEquiv___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_plEquiv___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_plEquiv___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Col_plEquiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_plEquiv___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_plEquiv___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Col_plEquiv___closed__1_value;
static const lean_ctor_object lp_tree_Formalism_L2_Col_plEquiv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Col_plEquiv___closed__0_value),((lean_object*)&lp_tree_Formalism_L2_Col_plEquiv___closed__1_value)}};
static const lean_object* lp_tree_Formalism_L2_Col_plEquiv___closed__2 = (const lean_object*)&lp_tree_Formalism_L2_Col_plEquiv___closed__2_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_idLat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_idLat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv___lam__0(lean_object* v_w_1_){
_start:
{
return v_w_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv___lam__1(lean_object* v_p_2_){
_start:
{
return v_p_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv(lean_object* v_K_8_, lean_object* v_inst_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = ((lean_object*)(lp_tree_Formalism_L2_Col_plEquiv___closed__2));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_plEquiv___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_L2_Col_plEquiv(v_K_12_, v_inst_13_, v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_idLat(lean_object* v_K_16_, lean_object* v_inst_17_, lean_object* v_I_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_idLat___boxed(lean_object* v_K_20_, lean_object* v_inst_21_, lean_object* v_I_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_Col_idLat(v_K_20_, v_inst_21_, v_I_22_);
lean_dec_ref(v_inst_21_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
