// Lean compiler output
// Module: Lib.General.LinearAlgebra.MinorProducts
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.FlenstedJensen.Defs public import Lib.General.Analysis.HolomorphicIntegrals
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
lean_object* lp_mathlib_Set_powersetCard_ofFinEmbEquiv___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_enumSubset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_enumSubset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_enumSubset___redArg(lean_object* v_k_1_, lean_object* v_inst_2_, lean_object* v_S_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v_toFun_7_; lean_object* v___x_8_; 
v___x_5_ = lp_mathlib_Set_powersetCard_ofFinEmbEquiv___redArg(v_k_1_, v_inst_2_);
v___x_6_ = lp_mathlib_Equiv_symm___redArg(v___x_5_);
v_toFun_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_toFun_7_);
lean_dec_ref(v___x_6_);
v___x_8_ = lean_apply_2(v_toFun_7_, v_S_3_, v_a_4_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_enumSubset(lean_object* v_I_9_, lean_object* v_k_10_, lean_object* v_inst_11_, lean_object* v_S_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_toFun_16_; lean_object* v___x_17_; 
v___x_14_ = lp_mathlib_Set_powersetCard_ofFinEmbEquiv___redArg(v_k_10_, v_inst_11_);
v___x_15_ = lp_mathlib_Equiv_symm___redArg(v___x_14_);
v_toFun_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_toFun_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_apply_2(v_toFun_16_, v_S_12_, v_a_13_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_LinearAlgebra_MinorProducts(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
