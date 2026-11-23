// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
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
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_conjInter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_conjInter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_conjInter(lean_object* v_G_1_, lean_object* v_inst_2_, lean_object* v_K_3_, lean_object* v_s_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_conjInter___boxed(lean_object* v_G_6_, lean_object* v_inst_7_, lean_object* v_K_8_, lean_object* v_s_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_UG_P_conjInter(v_G_6_, v_inst_7_, v_K_8_, v_s_9_);
lean_dec(v_s_9_);
lean_dec_ref(v_inst_7_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset(uint8_t builtin) {
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
