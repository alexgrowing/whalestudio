// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.StatementD
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.FinalC
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
lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowDeg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowWt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowWt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowWt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_dualLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_dualLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowWt___redArg(lean_object* v_n_1_, lean_object* v_m_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_tree_Formalism_GradedWeylDivisibility_rowDeg___redArg(v_n_1_, v_m_2_, v_a_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowWt(lean_object* v_k_5_, lean_object* v_n_6_, lean_object* v_m_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lp_tree_Formalism_GradedWeylDivisibility_rowDeg___redArg(v_n_6_, v_m_7_, v_a_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowWt___boxed(lean_object* v_k_10_, lean_object* v_n_11_, lean_object* v_m_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_GradedWeylDivisibility_rowWt(v_k_10_, v_n_11_, v_m_12_, v_a_13_);
lean_dec(v_k_10_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_dualLat(lean_object* v_R_15_, lean_object* v_K_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_V_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_M_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_dualLat___boxed(lean_object* v_R_27_, lean_object* v_K_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_V_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_M_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_GradedWeylDivisibility_dualLat(v_R_27_, v_K_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_V_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_inst_36_, v_M_37_);
lean_dec(v_inst_35_);
lean_dec(v_inst_34_);
lean_dec_ref(v_inst_33_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementD(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
