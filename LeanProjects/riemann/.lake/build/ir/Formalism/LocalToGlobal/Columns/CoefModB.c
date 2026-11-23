// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.CoefModB
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_DIV_mfact___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockB___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockB___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockB___redArg___lam__0(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_toMul_3_, lean_object* v_toNatCast_4_, lean_object* v_m_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
lean_inc_ref_n(v_m_5_, 2);
v___x_6_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_5_, v_f_1_);
v___x_7_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_5_, v_g_2_);
lean_inc(v_toMul_3_);
v___x_8_ = lean_apply_2(v_toMul_3_, v___x_6_, v___x_7_);
v___x_9_ = lp_tree_Formalism_L2_DIV_mfact___redArg(v_m_5_);
v___x_10_ = lean_apply_1(v_toNatCast_4_, v___x_9_);
v___x_11_ = lean_apply_2(v_toMul_3_, v___x_8_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockB___redArg(lean_object* v_inst_12_, lean_object* v_f_13_, lean_object* v_g_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toSemiring_17_; lean_object* v_toAddCommMonoid_18_; lean_object* v_support_19_; lean_object* v___x_20_; lean_object* v_toMul_21_; lean_object* v___x_22_; lean_object* v_toRing_23_; lean_object* v___x_24_; lean_object* v_toAddMonoidWithOne_25_; lean_object* v_toNatCast_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v___x_15_ = lp_mathlib_Field_toSemifield___redArg(v_inst_12_);
v___x_16_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_15_);
v_toSemiring_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v___x_16_);
v_toAddCommMonoid_18_ = lean_ctor_get(v_toSemiring_17_, 0);
lean_inc_ref(v_toAddCommMonoid_18_);
v_support_19_ = lean_ctor_get(v_f_13_, 0);
lean_inc(v_support_19_);
v___x_20_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_17_);
v_toMul_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_toMul_21_);
lean_dec_ref(v___x_20_);
v___x_22_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_12_);
v_toRing_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_toRing_23_);
lean_dec_ref(v___x_22_);
v___x_24_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_23_);
v_toAddMonoidWithOne_25_ = lean_ctor_get(v___x_24_, 1);
lean_inc_ref(v_toAddMonoidWithOne_25_);
lean_dec_ref(v___x_24_);
v_toNatCast_26_ = lean_ctor_get(v_toAddMonoidWithOne_25_, 0);
lean_inc(v_toNatCast_26_);
lean_dec_ref(v_toAddMonoidWithOne_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_fockB___redArg___lam__0), 5, 4);
lean_closure_set(v___f_27_, 0, v_f_13_);
lean_closure_set(v___f_27_, 1, v_g_14_);
lean_closure_set(v___f_27_, 2, v_toMul_21_);
lean_closure_set(v___f_27_, 3, v_toNatCast_26_);
v___x_28_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_18_, v_support_19_, v___f_27_);
lean_dec_ref(v_toAddCommMonoid_18_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockB(lean_object* v_K_29_, lean_object* v_inst_30_, lean_object* v_00_u03c3_31_, lean_object* v_f_32_, lean_object* v_g_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_L2_DIV_fockB___redArg(v_inst_30_, v_f_32_, v_g_33_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefModLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_PairingNondegenerateHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefModB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefModLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_PairingNondegenerateHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
