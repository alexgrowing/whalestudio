// Lean compiler output
// Module: Formalism.SatakeDualWeyl.StatementC
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.Statement
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
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_latS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_latS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_latS(lean_object* v_F_1_, lean_object* v_E_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_n_6_, lean_object* v_R_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_S_10_, lean_object* v_O_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_00_u039b_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_latS___boxed(lean_object* v_F_16_, lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_n_21_, lean_object* v_R_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_S_25_, lean_object* v_O_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_00_u039b_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_UG_latS(v_F_16_, v_E_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_n_21_, v_R_22_, v_inst_23_, v_inst_24_, v_S_25_, v_O_26_, v_inst_27_, v_inst_28_, v_00_u039b_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV___redArg___lam__0(lean_object* v_v_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_1(v_a_32_, v_v_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV___redArg(lean_object* v_v_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_evalV___redArg___lam__0), 2, 1);
lean_closure_set(v___f_35_, 0, v_v_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV(lean_object* v_F_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_v_39_){
_start:
{
lean_object* v___f_40_; 
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_evalV___redArg___lam__0), 2, 1);
lean_closure_set(v___f_40_, 0, v_v_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_evalV___boxed(lean_object* v_F_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_v_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_UG_evalV(v_F_41_, v_inst_42_, v_inst_43_, v_v_44_);
lean_dec_ref(v_inst_42_);
return v_res_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
