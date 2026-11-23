// Lean compiler output
// Module: Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_MtFam_loc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_AVTied_rep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_MtFam_loc(lean_object* v_D_1_, lean_object* v_M_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_nd_4_; lean_object* v_j_5_; lean_object* v_mu_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_nd_4_ = lean_ctor_get(v_D_1_, 41);
lean_inc_ref(v_nd_4_);
lean_dec_ref(v_D_1_);
v_j_5_ = lean_ctor_get(v_nd_4_, 5);
lean_inc_ref(v_j_5_);
v_mu_6_ = lean_ctor_get(v_nd_4_, 6);
lean_inc(v_mu_6_);
lean_dec_ref(v_nd_4_);
lean_inc(v_i_3_);
v___x_7_ = lean_apply_1(v_mu_6_, v_i_3_);
v___x_8_ = lean_apply_1(v_j_5_, v_i_3_);
v___x_9_ = lean_apply_4(v_M_2_, v___x_7_, v___x_8_, lean_box(0), lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_AVTied_rep(lean_object* v_D_10_, lean_object* v_M_11_, lean_object* v_A_12_, lean_object* v_i_13_, lean_object* v_P_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_wt_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc(v_i_13_);
v___x_15_ = lp_tree_Formalism_L2_MtFam_loc(v_D_10_, v_M_11_, v_i_13_);
v_wt_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_wt_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_apply_2(v_A_12_, v_i_13_, v_P_14_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_wt_16_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedHecke(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
