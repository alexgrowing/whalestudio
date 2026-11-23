// Lean compiler output
// Module: Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
// Imports: public import Init public meta import Init public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg public import Lemmata.ScalarExtension.Scal
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
lean_object* lp_mathlib_LinearMap_baseChange___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg___lam__0(lean_object* v_00_u03c1_1_, lean_object* v_toCommSemiring_2_, lean_object* v_toSemiring_3_, lean_object* v_inst_4_, lean_object* v_toAddMonoid_5_, lean_object* v_inst_6_, lean_object* v_g_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_81__overap_10_; lean_object* v___x_11_; 
v___x_9_ = lean_apply_1(v_00_u03c1_1_, v_g_7_);
lean_inc(v_inst_6_);
lean_inc_ref(v_toAddMonoid_5_);
v___x_81__overap_10_ = lp_mathlib_LinearMap_baseChange___redArg(v_toCommSemiring_2_, v_toSemiring_3_, v_inst_4_, v_toAddMonoid_5_, v_toAddMonoid_5_, v_inst_6_, v_inst_6_, v___x_9_);
v___x_11_ = lean_apply_1(v___x_81__overap_10_, v___y_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_00_u03c1_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toSemiring_20_; lean_object* v___x_21_; lean_object* v_toCommSemiring_22_; lean_object* v_toAddMonoid_23_; lean_object* v___f_24_; 
v___x_18_ = lp_mathlib_Field_toSemifield___redArg(v_inst_15_);
v___x_19_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_18_);
v_toSemiring_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_toSemiring_20_);
lean_dec_ref(v___x_19_);
v___x_21_ = lp_mathlib_Field_toSemifield___redArg(v_inst_12_);
v_toCommSemiring_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_toCommSemiring_22_);
lean_dec_ref(v___x_21_);
v_toAddMonoid_23_ = lean_ctor_get(v_inst_13_, 0);
lean_inc_ref(v_toAddMonoid_23_);
lean_dec_ref(v_inst_13_);
v___f_24_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg___lam__0), 8, 6);
lean_closure_set(v___f_24_, 0, v_00_u03c1_17_);
lean_closure_set(v___f_24_, 1, v_toCommSemiring_22_);
lean_closure_set(v___f_24_, 2, v_toSemiring_20_);
lean_closure_set(v___f_24_, 3, v_inst_16_);
lean_closure_set(v___f_24_, 4, v_toAddMonoid_23_);
lean_closure_set(v___f_24_, 5, v_inst_14_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg___boxed(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_00_u03c1_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg(v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_00_u03c1_30_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_25_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc(lean_object* v_k_32_, lean_object* v_G_33_, lean_object* v_V_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_K_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_00_u03c1_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___redArg(v_inst_35_, v_inst_37_, v_inst_38_, v_inst_40_, v_inst_41_, v_00_u03c1_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc___boxed(lean_object* v_k_44_, lean_object* v_G_45_, lean_object* v_V_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_K_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_00_u03c1_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_IrreducibleCountingLemmas_Z_BN_bc(v_k_44_, v_G_45_, v_V_46_, v_inst_47_, v_inst_48_, v_inst_49_, v_inst_50_, v_K_51_, v_inst_52_, v_inst_53_, v_00_u03c1_54_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg(uint8_t builtin);
lean_object* initialize_tree_Lemmata_ScalarExtension_Scal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_ScalarExtension_Scal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
