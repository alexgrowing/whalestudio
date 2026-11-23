// Lean compiler output
// Module: Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
// Imports: public import Init public meta import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_Sch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_Sch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___redArg___lam__0(lean_object* v_toAddSemigroup_1_, lean_object* v_a_2_, lean_object* v_00_u03a6_3_, lean_object* v_t_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_2(v_toAddSemigroup_1_, v_t_4_, v_a_2_);
v___x_6_ = lean_apply_1(v_00_u03a6_3_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___redArg(lean_object* v_inst_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_toAddMonoid_9_; lean_object* v_toAddSemigroup_10_; lean_object* v___f_11_; 
v_toAddMonoid_9_ = lean_ctor_get(v_inst_7_, 0);
lean_inc_ref(v_toAddMonoid_9_);
lean_dec_ref(v_inst_7_);
v_toAddSemigroup_10_ = lean_ctor_get(v_toAddMonoid_9_, 0);
lean_inc(v_toAddSemigroup_10_);
lean_dec_ref(v_toAddMonoid_9_);
v___f_11_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___redArg___lam__0), 4, 2);
lean_closure_set(v___f_11_, 0, v_toAddSemigroup_10_);
lean_closure_set(v___f_11_, 1, v_a_8_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA(lean_object* v_k_12_, lean_object* v_inst_13_, lean_object* v_A_14_, lean_object* v_inst_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___redArg(v_inst_15_, v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA___boxed(lean_object* v_k_18_, lean_object* v_inst_19_, lean_object* v_A_20_, lean_object* v_inst_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoA(v_k_18_, v_inst_19_, v_A_20_, v_inst_21_, v_a_22_);
lean_dec_ref(v_inst_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg___lam__0(lean_object* v_c_24_, lean_object* v_b_25_, lean_object* v_toMul_26_, lean_object* v_00_u03a6_27_, lean_object* v_t_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
lean_inc(v_t_28_);
v___x_29_ = lean_apply_2(v_c_24_, v_b_25_, v_t_28_);
v___x_30_ = lean_apply_1(v_00_u03a6_27_, v_t_28_);
v___x_31_ = lean_apply_2(v_toMul_26_, v___x_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg(lean_object* v_inst_32_, lean_object* v_c_33_, lean_object* v_b_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v_toSemiring_37_; lean_object* v___x_38_; lean_object* v_toMul_39_; lean_object* v___f_40_; 
v___x_35_ = lp_mathlib_Field_toSemifield___redArg(v_inst_32_);
v___x_36_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_35_);
v_toSemiring_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc_ref(v_toSemiring_37_);
lean_dec_ref(v___x_36_);
v___x_38_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_37_);
v_toMul_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_toMul_39_);
lean_dec_ref(v___x_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg___lam__0), 5, 3);
lean_closure_set(v___f_40_, 0, v_c_33_);
lean_closure_set(v___f_40_, 1, v_b_34_);
lean_closure_set(v___f_40_, 2, v_toMul_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg___boxed(lean_object* v_inst_41_, lean_object* v_c_42_, lean_object* v_b_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg(v_inst_41_, v_c_42_, v_b_43_);
lean_dec_ref(v_inst_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB(lean_object* v_k_45_, lean_object* v_inst_46_, lean_object* v_A_47_, lean_object* v_B_48_, lean_object* v_c_49_, lean_object* v_b_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___redArg(v_inst_46_, v_c_49_, v_b_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB___boxed(lean_object* v_k_52_, lean_object* v_inst_53_, lean_object* v_A_54_, lean_object* v_B_55_, lean_object* v_c_56_, lean_object* v_b_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_L2_PairingIndexBounds_Mv_rhoB(v_k_52_, v_inst_53_, v_A_54_, v_B_55_, v_c_56_, v_b_57_);
lean_dec_ref(v_inst_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_Sch(lean_object* v_k_59_, lean_object* v_inst_60_, lean_object* v_A_61_, lean_object* v_B_62_, lean_object* v_inst_63_, lean_object* v_c_64_, lean_object* v_A_u2080_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PairingIndexBounds_Mv_Sch___boxed(lean_object* v_k_67_, lean_object* v_inst_68_, lean_object* v_A_69_, lean_object* v_B_70_, lean_object* v_inst_71_, lean_object* v_c_72_, lean_object* v_A_u2080_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_L2_PairingIndexBounds_Mv_Sch(v_k_67_, v_inst_68_, v_A_69_, v_B_70_, v_inst_71_, v_c_72_, v_A_u2080_73_);
lean_dec(v_c_72_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_68_);
return v_res_74_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_IsBichar(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
