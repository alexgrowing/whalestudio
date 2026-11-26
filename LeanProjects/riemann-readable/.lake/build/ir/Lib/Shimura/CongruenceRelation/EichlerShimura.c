// Lean compiler output
// Module: Lib.Shimura.CongruenceRelation.EichlerShimura
// Imports: public import Init public meta import Init public import Lib.Cohomology.SmoothBaseChange
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
lean_object* lp_GRH_New_Variety_frobPow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0(lean_object* v_U_1_, lean_object* v_p_2_, lean_object* v_j_3_, lean_object* v_B_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_map_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_map_6_ = lean_ctor_get(v_U_1_, 1);
lean_inc(v_map_6_);
lean_dec_ref(v_U_1_);
v___x_7_ = lp_GRH_New_Variety_frobPow___redArg(v_p_2_, v_B_4_, v_j_3_);
lean_inc_ref(v_B_4_);
v___x_8_ = lean_apply_4(v_map_6_, v_B_4_, v_B_4_, v___x_7_, v___y_5_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0___boxed(lean_object* v_U_9_, lean_object* v_p_10_, lean_object* v_j_11_, lean_object* v_B_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0(v_U_9_, v_p_10_, v_j_11_, v_B_12_, v___y_13_);
lean_dec(v_j_11_);
lean_dec(v_p_10_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg(lean_object* v_p_15_, lean_object* v_U_16_, lean_object* v_j_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_18_, 0, v_U_16_);
lean_closure_set(v___f_18_, 1, v_p_15_);
lean_closure_set(v___f_18_, 2, v_j_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ellAdicCohom_frobEnd(lean_object* v_p_19_, lean_object* v_inst_20_, lean_object* v_U_21_, lean_object* v_hU__char_22_, lean_object* v_j_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_ellAdicCohom_frobEnd___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_24_, 0, v_U_21_);
lean_closure_set(v___f_24_, 1, v_p_19_);
lean_closure_set(v___f_24_, 2, v_j_23_);
return v___f_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_SmoothBaseChange(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_CongruenceRelation_EichlerShimura(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_SmoothBaseChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
