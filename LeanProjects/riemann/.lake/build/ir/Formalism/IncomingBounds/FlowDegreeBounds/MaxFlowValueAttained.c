// Lean compiler output
// Module: Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.IncomingBounds.IncomingBound
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
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instNatCast;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_IncomingBounds_oddLevels(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_IncomingBounds_flowVal___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_trunc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_trunc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___lam__0(lean_object* v_l_1_, lean_object* v___f_2_, lean_object* v_x_3_, lean_object* v_s_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_641__overap_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; 
v___x_641__overap_6_ = lp_mathlib_Real_instNatCast;
v___x_7_ = lean_apply_1(v___x_641__overap_6_, v_l_1_);
v___x_8_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_9_ = l_npowRec___redArg(v___x_8_, v___f_2_, v_i_5_, v___x_7_);
v___x_10_ = lean_apply_2(v_x_3_, v_s_4_, v_i_5_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v___x_9_);
lean_closure_set(v___f_11_, 1, v___x_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___lam__1(lean_object* v_toNatCast_12_, lean_object* v_toSub_13_, lean_object* v_s_14_, lean_object* v_x_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_inc(v_i_16_);
v___x_17_ = lean_apply_1(v_toNatCast_12_, v_i_16_);
v___x_18_ = lean_apply_2(v_toSub_13_, v_s_14_, v___x_17_);
v___x_19_ = lean_apply_2(v_x_15_, v___x_18_, v_i_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg(lean_object* v_l_21_, lean_object* v_d_22_, lean_object* v_x_23_, lean_object* v_s_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v_toAddMonoidWithOne_29_; lean_object* v_toSub_30_; lean_object* v_toNatCast_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___f_38_; 
v___x_25_ = lp_mathlib_Real_instAddCommMonoid;
lean_inc(v_d_22_);
v___x_26_ = lp_mathlib_ZMod_commRing(v_d_22_);
v___x_27_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_26_);
v___x_28_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_27_);
v_toAddMonoidWithOne_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc_ref(v_toAddMonoidWithOne_29_);
lean_dec_ref(v___x_27_);
v_toSub_30_ = lean_ctor_get(v___x_28_, 2);
lean_inc(v_toSub_30_);
lean_dec_ref(v___x_28_);
v_toNatCast_31_ = lean_ctor_get(v_toAddMonoidWithOne_29_, 0);
lean_inc(v_toNatCast_31_);
lean_dec_ref(v_toAddMonoidWithOne_29_);
v___f_32_ = ((lean_object*)(lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___closed__0));
lean_inc(v_s_24_);
lean_inc(v_x_23_);
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___lam__0), 5, 4);
lean_closure_set(v___f_33_, 0, v_l_21_);
lean_closure_set(v___f_33_, 1, v___f_32_);
lean_closure_set(v___f_33_, 2, v_x_23_);
lean_closure_set(v___f_33_, 3, v_s_24_);
v___x_34_ = lp_tree_Formalism_IncomingBounds_oddLevels(v_d_22_);
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg___lam__1), 5, 4);
lean_closure_set(v___f_35_, 0, v_toNatCast_31_);
lean_closure_set(v___f_35_, 1, v_toSub_30_);
lean_closure_set(v___f_35_, 2, v_s_24_);
lean_closure_set(v___f_35_, 3, v_x_23_);
lean_inc(v___x_34_);
v___x_36_ = lp_mathlib_Finset_sum___redArg(v___x_25_, v___x_34_, v___f_33_);
v___x_37_ = lp_mathlib_Finset_sum___redArg(v___x_25_, v___x_34_, v___f_35_);
v___f_38_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_38_, 0, v___x_36_);
lean_closure_set(v___f_38_, 1, v___x_37_);
return v___f_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad(lean_object* v_l_39_, lean_object* v_d_40_, lean_object* v_inst_41_, lean_object* v_x_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg(v_l_39_, v_d_40_, v_x_42_, v_s_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_trunc___redArg(lean_object* v_d_45_, lean_object* v_x_46_, lean_object* v_s_47_, lean_object* v_i_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_49_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_50_ = lp_tree_Formalism_IncomingBounds_oddLevels(v_d_45_);
lean_inc(v_i_48_);
v___x_51_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_49_, v_i_48_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec(v_i_48_);
lean_dec(v_s_47_);
lean_dec(v_x_46_);
v___x_52_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_52_;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = lean_apply_2(v_x_46_, v_s_47_, v_i_48_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_trunc(lean_object* v_d_54_, lean_object* v_inst_55_, lean_object* v_x_56_, lean_object* v_s_57_, lean_object* v_i_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_IncomingBounds_FlowLoadBounds_trunc___redArg(v_d_54_, v_x_56_, v_s_57_, v_i_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap___redArg___lam__0(lean_object* v_l_60_, lean_object* v_d_61_, lean_object* v_x_62_, lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_tree_Formalism_IncomingBounds_FlowLoadBounds_dpLoad___redArg(v_l_60_, v_d_61_, v_x_62_, v_s_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap___redArg(lean_object* v_l_65_, lean_object* v_d_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_inc(v_x_67_);
lean_inc(v_d_66_);
v___f_68_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_68_, 0, v_l_65_);
lean_closure_set(v___f_68_, 1, v_d_66_);
lean_closure_set(v___f_68_, 2, v_x_67_);
v___x_69_ = lp_tree_Formalism_IncomingBounds_flowVal___redArg(v_d_66_, v_x_67_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___f_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap(lean_object* v_l_71_, lean_object* v_d_72_, lean_object* v_inst_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_tree_Formalism_IncomingBounds_FlowLoadBounds_gmap___redArg(v_l_71_, v_d_72_, v_x_74_);
return v___x_75_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_IncomingBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained(uint8_t builtin) {
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
res = initialize_tree_Formalism_IncomingBounds_IncomingBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
