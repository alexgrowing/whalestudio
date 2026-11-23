// Lean compiler output
// Module: Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum public import Formalism.FrobeniusOrbits.HostDiffSupport
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_condN(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_condN___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_condN(lean_object* v_e_1_, lean_object* v_q_2_, lean_object* v_d_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_add(v_e_1_, v___x_4_);
v___x_6_ = lean_nat_pow(v___x_4_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_nat_mul(v___x_6_, v_q_2_);
lean_dec(v___x_6_);
v___x_8_ = lean_nat_mul(v___x_7_, v_d_3_);
lean_dec(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_condN___boxed(lean_object* v_e_9_, lean_object* v_q_10_, lean_object* v_d_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_Host_condN(v_e_9_, v_q_10_, v_d_11_);
lean_dec(v_d_11_);
lean_dec(v_q_10_);
lean_dec(v_e_9_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
