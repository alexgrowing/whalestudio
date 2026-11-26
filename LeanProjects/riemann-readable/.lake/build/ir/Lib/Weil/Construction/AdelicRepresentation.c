// Lean compiler output
// Module: Lib.Weil.Construction.AdelicRepresentation
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.RationalPoints public import Lib.Weil.Construction.FiniteCocycle public import Lib.Weil.Fock.Basic
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
LEAN_EXPORT lean_object* lp_GRH_New_realSigns___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_realSigns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_realSigns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_realSigns___redArg(lean_object* v_s_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_snd_3_; lean_object* v___x_4_; 
v_snd_3_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_3_);
lean_dec_ref(v_p_2_);
v___x_4_ = lean_apply_1(v_s_1_, v_snd_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_realSigns(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_n_7_, lean_object* v_s_8_, lean_object* v_p_9_){
_start:
{
lean_object* v_snd_10_; lean_object* v___x_11_; 
v_snd_10_ = lean_ctor_get(v_p_9_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v_p_9_);
v___x_11_ = lean_apply_1(v_s_8_, v_snd_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_realSigns___boxed(lean_object* v_E_12_, lean_object* v_inst_13_, lean_object* v_n_14_, lean_object* v_s_15_, lean_object* v_p_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_GRH_New_realSigns(v_E_12_, v_inst_13_, v_n_14_, v_s_15_, v_p_16_);
lean_dec_ref(v_inst_13_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_RationalPoints(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_FiniteCocycle(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Fock_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Construction_AdelicRepresentation(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_RationalPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Construction_FiniteCocycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Fock_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
