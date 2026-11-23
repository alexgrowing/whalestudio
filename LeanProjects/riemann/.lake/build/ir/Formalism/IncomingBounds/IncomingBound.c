// Lean compiler output
// Module: Formalism.IncomingBounds.IncomingBound
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
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lp_mathlib_Nat_instDecidablePredOdd(lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_oddLevels(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_Dl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0_spec__1(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_15_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_15_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
uint8_t v___x_9_; 
v___x_9_ = lp_mathlib_Nat_instDecidablePredOdd(v_head_4_);
if (v___x_9_ == 0)
{
lean_del_object(v___x_7_);
lean_dec(v_head_4_);
v_a_1_ = v_tail_5_;
goto _start;
}
else
{
lean_object* v___x_12_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_head_4_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_a_2_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_12_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0___redArg(lean_object* v_s_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_box(0);
v___x_18_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0_spec__1(v_s_16_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_oddLevels(lean_object* v_d_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = l_List_range(v_d_19_);
v___x_21_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0___redArg(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0___redArg(lean_object* v_s_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0___redArg(v_s_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0(lean_object* v_p_24_, lean_object* v_s_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0___redArg(v_s_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0(lean_object* v_p_27_, lean_object* v_s_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_IncomingBounds_oddLevels_spec__0_spec__0___redArg(v_s_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__0(lean_object* v_x_30_, lean_object* v_s_31_, lean_object* v_i_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_2(v_x_30_, v_s_31_, v_i_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__1(lean_object* v_x_34_, lean_object* v_d_35_, lean_object* v___x_36_, lean_object* v_s_37_){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___f_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_38_, 0, v_x_34_);
lean_closure_set(v___f_38_, 1, v_s_37_);
v___x_39_ = lp_tree_Formalism_IncomingBounds_oddLevels(v_d_35_);
v___x_40_ = lp_mathlib_Finset_sum___redArg(v___x_36_, v___x_39_, v___f_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__1___boxed(lean_object* v_x_41_, lean_object* v_d_42_, lean_object* v___x_43_, lean_object* v_s_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__1(v_x_41_, v_d_42_, v___x_43_, v_s_44_);
lean_dec_ref(v___x_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg(lean_object* v_d_46_, lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = lp_mathlib_Real_instAddCommMonoid;
lean_inc(v_d_46_);
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_flowVal___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_49_, 0, v_x_47_);
lean_closure_set(v___f_49_, 1, v_d_46_);
lean_closure_set(v___f_49_, 2, v___x_48_);
v___x_50_ = lp_mathlib_ZMod_fintype___redArg(v_d_46_);
lean_dec(v_d_46_);
v___x_51_ = lp_mathlib_Finset_sum___redArg(v___x_48_, v___x_50_, v___f_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_flowVal(lean_object* v_d_52_, lean_object* v_inst_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_Formalism_IncomingBounds_flowVal___redArg(v_d_52_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capL(lean_object* v_d_56_, lean_object* v_TT_57_, lean_object* v_nu1_58_, lean_object* v_nu2_59_, lean_object* v_s_60_){
_start:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_61_, 0, v_d_56_);
lean_inc(v_s_60_);
v___x_62_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_61_, v_s_60_, v_TT_57_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v_nu2_59_);
v___x_63_ = lean_apply_1(v_nu1_58_, v_s_60_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
lean_dec_ref(v_nu1_58_);
v___x_64_ = lean_apply_1(v_nu2_59_, v_s_60_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_Dl(lean_object* v_d_65_, lean_object* v_TT_66_, lean_object* v_nu1_67_, lean_object* v_size_68_, lean_object* v_s_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_70_, 0, v_d_65_);
lean_inc(v_s_69_);
v___x_71_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_70_, v_s_69_, v_TT_66_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_nu1_67_);
v___x_72_ = lean_apply_1(v_size_68_, v_s_69_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc(v_s_69_);
v___x_73_ = lean_apply_1(v_size_68_, v_s_69_);
v___x_74_ = lean_apply_1(v_nu1_67_, v_s_69_);
v___x_75_ = lean_nat_sub(v___x_73_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v___x_73_);
return v___x_75_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_IncomingBounds_IncomingBound(uint8_t builtin) {
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
