// Lean compiler output
// Module: Formalism.CyclotomicNorms.NonsquarefreeBounds.AdaptiveSubstitutionBound
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.DiscardKernel public import Formalism.CyclotomicNorms.NonsquarefreeBounds.SubstitutionBound
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_List_sum___at___00Nat_zeckendorfEquiv_spec__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_CyclotomicNorms_AdaptiveSubstitution_step_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_CyclotomicNorms_AdaptiveSubstitution_step_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_CyclotomicNorms_AdaptiveSubstitution_step_spec__0(lean_object* v_00_u2113_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
v___x_4_ = l_List_reverse___redArg(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_15_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_15_ == 0)
{
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_10_ = lean_nat_pow(v_00_u2113_1_, v_head_5_);
lean_dec(v_head_5_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_a_3_);
lean_ctor_set(v___x_8_, 0, v___x_10_);
v___x_12_ = v___x_8_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_a_3_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_12_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_CyclotomicNorms_AdaptiveSubstitution_step_spec__0___boxed(lean_object* v_00_u2113_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_List_mapTR_loop___at___00Formalism_CyclotomicNorms_AdaptiveSubstitution_step_spec__0(v_00_u2113_16_, v_a_17_, v_a_18_);
lean_dec(v_00_u2113_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_step(lean_object* v_00_u2113_20_, lean_object* v_A_21_, lean_object* v_B_22_, lean_object* v_L_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
lean_inc_n(v_L_23_, 2);
v___x_24_ = lean_apply_1(v_B_22_, v_L_23_);
v___x_25_ = lean_box(0);
v___x_26_ = lp_tree_List_mapTR_loop___at___00Formalism_CyclotomicNorms_AdaptiveSubstitution_step_spec__0(v_00_u2113_20_, v_L_23_, v___x_25_);
v___x_27_ = lp_mathlib_List_sum___at___00Nat_zeckendorfEquiv_spec__1(v___x_26_);
lean_dec(v___x_26_);
v___x_28_ = lean_nat_mul(v_A_21_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_add(v___x_24_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_24_);
v___x_30_ = lp_mathlib_List_sum___at___00Nat_zeckendorfEquiv_spec__1(v_L_23_);
lean_dec(v_L_23_);
v___x_31_ = lean_nat_add(v___x_29_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_add(v___x_31_, v___x_32_);
lean_dec(v___x_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_step___boxed(lean_object* v_00_u2113_34_, lean_object* v_A_35_, lean_object* v_B_36_, lean_object* v_L_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_step(v_00_u2113_34_, v_A_35_, v_B_36_, v_L_37_);
lean_dec(v_A_35_);
lean_dec(v_00_u2113_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre(lean_object* v_00_u2113_39_, lean_object* v_A_40_, lean_object* v_B_41_, lean_object* v_x_42_){
_start:
{
lean_object* v_zero_43_; uint8_t v_isZero_44_; 
v_zero_43_ = lean_unsigned_to_nat(0u);
v_isZero_44_ = lean_nat_dec_eq(v_x_42_, v_zero_43_);
if (v_isZero_44_ == 1)
{
lean_object* v___x_45_; 
lean_dec_ref(v_B_41_);
v___x_45_ = lean_box(0);
return v___x_45_;
}
else
{
lean_object* v_one_46_; lean_object* v_n_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_one_46_ = lean_unsigned_to_nat(1u);
v_n_47_ = lean_nat_sub(v_x_42_, v_one_46_);
lean_inc_ref(v_B_41_);
v___x_48_ = lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre(v_00_u2113_39_, v_A_40_, v_B_41_, v_n_47_);
lean_dec(v_n_47_);
lean_inc(v___x_48_);
v___x_49_ = lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_step(v_00_u2113_39_, v_A_40_, v_B_41_, v___x_48_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = l_List_appendTR___redArg(v___x_48_, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre___boxed(lean_object* v_00_u2113_53_, lean_object* v_A_54_, lean_object* v_B_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre(v_00_u2113_53_, v_A_54_, v_B_55_, v_x_56_);
lean_dec(v_x_56_);
lean_dec(v_A_54_);
lean_dec(v_00_u2113_53_);
return v_res_57_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_DiscardKernel(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_DiscardKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
