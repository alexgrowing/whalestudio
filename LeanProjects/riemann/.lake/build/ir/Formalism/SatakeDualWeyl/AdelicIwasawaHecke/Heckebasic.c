// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
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
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs___redArg___lam__0(lean_object* v_c_1_, lean_object* v_g_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v_c_1_, 1);
lean_inc(v_toFun_3_);
lean_dec_ref(v_c_1_);
v___x_4_ = lean_apply_1(v_toFun_3_, v_g_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs___redArg(lean_object* v_c_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_ofFs___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_c_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs(lean_object* v_G_7_, lean_object* v_inst_8_, lean_object* v_k_9_, lean_object* v_inst_10_, lean_object* v_K_11_, lean_object* v_c_12_){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_ofFs___redArg___lam__0), 2, 1);
lean_closure_set(v___f_13_, 0, v_c_12_);
return v___f_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_ofFs___boxed(lean_object* v_G_14_, lean_object* v_inst_15_, lean_object* v_k_16_, lean_object* v_inst_17_, lean_object* v_K_18_, lean_object* v_c_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_UG_P_ofFs(v_G_14_, v_inst_15_, v_k_16_, v_inst_17_, v_K_18_, v_c_19_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_15_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic(uint8_t builtin) {
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
