// Lean compiler output
// Module: Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun___redArg(lean_object* v_inst_1_, lean_object* v_C_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_toSemiring_6_; lean_object* v___x_7_; lean_object* v_toMonoid_8_; 
v___x_4_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_5_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_4_);
v_toSemiring_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref_n(v_toSemiring_6_, 2);
lean_dec_ref(v___x_5_);
v___x_7_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_6_);
v_toMonoid_8_ = lean_ctor_get(v_toSemiring_6_, 1);
lean_inc_ref(v_toMonoid_8_);
lean_dec_ref(v_toSemiring_6_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v_toMonoid_8_);
lean_dec_ref(v___x_7_);
lean_dec_ref(v_C_2_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v_u_10_; lean_object* v_toMul_11_; lean_object* v_toAdd_12_; lean_object* v_toNPow_13_; lean_object* v_x_14_; lean_object* v_y_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_37_; 
v_u_10_ = lean_ctor_get(v_C_2_, 0);
lean_inc_ref(v_u_10_);
v_toMul_11_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_toMul_11_);
v_toAdd_12_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toAdd_12_);
lean_dec_ref(v___x_7_);
v_toNPow_13_ = lean_ctor_get(v_toMonoid_8_, 2);
lean_inc(v_toNPow_13_);
lean_dec_ref(v_toMonoid_8_);
v_x_14_ = lean_ctor_get(v_x_3_, 0);
v_y_15_ = lean_ctor_get(v_x_3_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_37_ == 0)
{
v___x_17_ = v_x_3_;
v_isShared_18_ = v_isSharedCheck_37_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_y_15_);
lean_inc(v_x_14_);
lean_dec(v_x_3_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_37_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_r_19_; lean_object* v_s_20_; lean_object* v_t_21_; lean_object* v_val_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v_r_19_ = lean_ctor_get(v_C_2_, 1);
lean_inc(v_r_19_);
v_s_20_ = lean_ctor_get(v_C_2_, 2);
lean_inc(v_s_20_);
v_t_21_ = lean_ctor_get(v_C_2_, 3);
lean_inc(v_t_21_);
lean_dec_ref(v_C_2_);
v_val_22_ = lean_ctor_get(v_u_10_, 0);
lean_inc_n(v_val_22_, 2);
lean_dec_ref(v_u_10_);
v___x_23_ = lean_unsigned_to_nat(2u);
lean_inc(v_toNPow_13_);
v___x_24_ = lean_apply_2(v_toNPow_13_, v___x_23_, v_val_22_);
lean_inc_n(v_toMul_11_, 3);
lean_inc(v_x_14_);
lean_inc(v___x_24_);
v___x_25_ = lean_apply_2(v_toMul_11_, v___x_24_, v_x_14_);
lean_inc_n(v_toAdd_12_, 2);
v___x_26_ = lean_apply_2(v_toAdd_12_, v___x_25_, v_r_19_);
v___x_27_ = lean_unsigned_to_nat(3u);
v___x_28_ = lean_apply_2(v_toNPow_13_, v___x_27_, v_val_22_);
v___x_29_ = lean_apply_2(v_toMul_11_, v___x_28_, v_y_15_);
v___x_30_ = lean_apply_2(v_toMul_11_, v___x_24_, v_s_20_);
v___x_31_ = lean_apply_2(v_toMul_11_, v___x_30_, v_x_14_);
v___x_32_ = lean_apply_2(v_toAdd_12_, v___x_29_, v___x_31_);
v___x_33_ = lean_apply_2(v_toAdd_12_, v___x_32_, v_t_21_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_33_);
lean_ctor_set(v___x_17_, 0, v___x_26_);
v___x_35_ = v___x_17_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun___redArg___boxed(lean_object* v_inst_38_, lean_object* v_C_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_GlobalTheory_variableChangePointFun___redArg(v_inst_38_, v_C_39_, v_x_40_);
lean_dec_ref(v_inst_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun(lean_object* v_k_42_, lean_object* v_inst_43_, lean_object* v_W_44_, lean_object* v_W_x27_45_, lean_object* v_C_46_, lean_object* v_h_47_, lean_object* v_x_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_tree_GlobalTheory_variableChangePointFun___redArg(v_inst_43_, v_C_46_, v_x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePointFun___boxed(lean_object* v_k_50_, lean_object* v_inst_51_, lean_object* v_W_52_, lean_object* v_W_x27_53_, lean_object* v_C_54_, lean_object* v_h_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_GlobalTheory_variableChangePointFun(v_k_50_, v_inst_51_, v_W_52_, v_W_x27_53_, v_C_54_, v_h_55_, v_x_56_);
lean_dec_ref(v_W_x27_53_);
lean_dec_ref(v_W_52_);
lean_dec_ref(v_inst_51_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter___redArg(lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_60_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__1_59_, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v_x_63_; lean_object* v_y_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_59_);
v_x_63_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_x_63_);
v_y_64_ = lean_ctor_get(v_x_58_, 1);
lean_inc(v_y_64_);
lean_dec_ref_known(v_x_58_, 2);
v___x_65_ = lean_apply_3(v_h__2_60_, v_x_63_, v_y_64_, lean_box(0));
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter(lean_object* v_k_66_, lean_object* v_inst_67_, lean_object* v_W_x27_68_, lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_72_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__1_71_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_x_75_; lean_object* v_y_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_71_);
v_x_75_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_x_75_);
v_y_76_ = lean_ctor_get(v_x_70_, 1);
lean_inc(v_y_76_);
lean_dec_ref_known(v_x_70_, 2);
v___x_77_ = lean_apply_3(v_h__2_72_, v_x_75_, v_y_76_, lean_box(0));
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter___boxed(lean_object* v_k_78_, lean_object* v_inst_79_, lean_object* v_W_x27_80_, lean_object* v_motive_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_tree___private_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero_0__GlobalTheory_variableChangePointFun_match__1_splitter(v_k_78_, v_inst_79_, v_W_x27_80_, v_motive_81_, v_x_82_, v_h__1_83_, v_h__2_84_);
lean_dec_ref(v_W_x27_80_);
lean_dec_ref(v_inst_79_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePoint___redArg(lean_object* v_inst_86_, lean_object* v_W_87_, lean_object* v_W_x27_88_, lean_object* v_C_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_variableChangePointFun___boxed), 7, 6);
lean_closure_set(v___x_90_, 0, lean_box(0));
lean_closure_set(v___x_90_, 1, v_inst_86_);
lean_closure_set(v___x_90_, 2, v_W_87_);
lean_closure_set(v___x_90_, 3, v_W_x27_88_);
lean_closure_set(v___x_90_, 4, v_C_89_);
lean_closure_set(v___x_90_, 5, lean_box(0));
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePoint(lean_object* v_k_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_W_94_, lean_object* v_W_x27_95_, lean_object* v_C_96_, lean_object* v_h_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_variableChangePointFun___boxed), 7, 6);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, v_inst_92_);
lean_closure_set(v___x_98_, 2, v_W_94_);
lean_closure_set(v___x_98_, 3, v_W_x27_95_);
lean_closure_set(v___x_98_, 4, v_C_96_);
lean_closure_set(v___x_98_, 5, lean_box(0));
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_variableChangePoint___boxed(lean_object* v_k_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_W_102_, lean_object* v_W_x27_103_, lean_object* v_C_104_, lean_object* v_h_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_GlobalTheory_variableChangePoint(v_k_99_, v_inst_100_, v_inst_101_, v_W_102_, v_W_x27_103_, v_C_104_, v_h_105_);
lean_dec_ref(v_inst_101_);
return v_res_106_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero(uint8_t builtin) {
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
