// Lean compiler output
// Module: Lib.Shimura.ThetaGroup
// Imports: public import Init public meta import Init public import Lib.Shimura.AbelianScheme.Pairings
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection___redArg___lam__0(lean_object* v_L_1_, lean_object* v_j_2_, lean_object* v_i_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_transition_6_; lean_object* v___x_7_; 
v_transition_6_ = lean_ctor_get(v_L_1_, 1);
lean_inc(v_transition_6_);
lean_dec_ref(v_L_1_);
v___x_7_ = lean_apply_4(v_transition_6_, v_i_3_, v_j_2_, v___y_4_, v___y_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection___redArg(lean_object* v_L_8_, lean_object* v_j_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_coordSection___redArg___lam__0), 5, 2);
lean_closure_set(v___f_10_, 0, v_L_8_);
lean_closure_set(v___f_10_, 1, v_j_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection(lean_object* v_R_11_, lean_object* v_inst_12_, lean_object* v_X_13_, lean_object* v_00_u03b9_14_, lean_object* v_L_15_, lean_object* v_h_16_, lean_object* v_j_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_coordSection___redArg___lam__0), 5, 2);
lean_closure_set(v___f_18_, 0, v_L_15_);
lean_closure_set(v___f_18_, 1, v_j_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_coordSection___boxed(lean_object* v_R_19_, lean_object* v_inst_20_, lean_object* v_X_21_, lean_object* v_00_u03b9_22_, lean_object* v_L_23_, lean_object* v_h_24_, lean_object* v_j_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Variety_coordSection(v_R_19_, v_inst_20_, v_X_21_, v_00_u03b9_22_, v_L_23_, v_h_24_, v_j_25_);
lean_dec_ref(v_X_21_);
lean_dec_ref(v_inst_20_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_AbelianScheme_Pairings(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ThetaGroup(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_AbelianScheme_Pairings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
