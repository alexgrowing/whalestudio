// Lean compiler output
// Module: Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasRationalTorsionIffMemRange
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_splitCurve___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_splitCurve(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_legendreCurve___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_legendreCurve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_deuringCurve___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_deuringCurve(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_splitCurve___redArg(lean_object* v_inst_1_, lean_object* v_A_2_, lean_object* v_B_3_){
_start:
{
lean_object* v_toSemiring_4_; lean_object* v___x_5_; lean_object* v_toZero_6_; lean_object* v___x_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_22_; 
v_toSemiring_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref_n(v_toSemiring_4_, 2);
v___x_5_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_4_);
v_toZero_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_toZero_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_1_);
v_isSharedCheck_22_ = !lean_is_exclusive(v_inst_1_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; lean_object* v_unused_24_; lean_object* v_unused_25_; lean_object* v_unused_26_; lean_object* v_unused_27_; 
v_unused_23_ = lean_ctor_get(v_inst_1_, 4);
lean_dec(v_unused_23_);
v_unused_24_ = lean_ctor_get(v_inst_1_, 3);
lean_dec(v_unused_24_);
v_unused_25_ = lean_ctor_get(v_inst_1_, 2);
lean_dec(v_unused_25_);
v_unused_26_ = lean_ctor_get(v_inst_1_, 1);
lean_dec(v_unused_26_);
v_unused_27_ = lean_ctor_get(v_inst_1_, 0);
lean_dec(v_unused_27_);
v___x_9_ = v_inst_1_;
v_isShared_10_ = v_isSharedCheck_22_;
goto v_resetjp_8_;
}
else
{
lean_dec(v_inst_1_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_22_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v_toNeg_12_; lean_object* v___x_13_; lean_object* v_toMul_14_; lean_object* v_toAdd_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_11_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_7_);
lean_dec_ref(v___x_7_);
v_toNeg_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_toNeg_12_);
lean_dec_ref(v___x_11_);
v___x_13_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_4_);
v_toMul_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_toMul_14_);
v_toAdd_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_toAdd_15_);
lean_dec_ref(v___x_13_);
lean_inc(v_B_3_);
lean_inc(v_A_2_);
v___x_16_ = lean_apply_2(v_toAdd_15_, v_A_2_, v_B_3_);
v___x_17_ = lean_apply_1(v_toNeg_12_, v___x_16_);
v___x_18_ = lean_apply_2(v_toMul_14_, v_A_2_, v_B_3_);
lean_inc_n(v_toZero_6_, 2);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 4, v_toZero_6_);
lean_ctor_set(v___x_9_, 3, v___x_18_);
lean_ctor_set(v___x_9_, 2, v_toZero_6_);
lean_ctor_set(v___x_9_, 1, v___x_17_);
lean_ctor_set(v___x_9_, 0, v_toZero_6_);
v___x_20_ = v___x_9_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_toZero_6_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 2, v_toZero_6_);
lean_ctor_set(v_reuseFailAlloc_21_, 3, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_21_, 4, v_toZero_6_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_splitCurve(lean_object* v_R_28_, lean_object* v_inst_29_, lean_object* v_A_30_, lean_object* v_B_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_tree_GlobalTheory_splitCurve___redArg(v_inst_29_, v_A_30_, v_B_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_legendreCurve___redArg(lean_object* v_inst_33_, lean_object* v_l_34_){
_start:
{
lean_object* v_toSemiring_35_; lean_object* v___x_36_; lean_object* v_toZero_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v_toNeg_40_; lean_object* v___x_41_; lean_object* v_toAdd_42_; lean_object* v___x_43_; lean_object* v_toAddMonoidWithOne_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_54_; 
v_toSemiring_35_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref_n(v_toSemiring_35_, 2);
v___x_36_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_35_);
v_toZero_37_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_toZero_37_);
lean_dec_ref(v___x_36_);
v___x_38_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_33_);
v___x_39_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_38_);
lean_dec_ref(v___x_38_);
v_toNeg_40_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_toNeg_40_);
lean_dec_ref(v___x_39_);
v___x_41_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_35_);
v_toAdd_42_ = lean_ctor_get(v___x_41_, 1);
lean_inc(v_toAdd_42_);
lean_dec_ref(v___x_41_);
v___x_43_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_33_);
v_toAddMonoidWithOne_44_ = lean_ctor_get(v___x_43_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; lean_object* v_unused_56_; lean_object* v_unused_57_; lean_object* v_unused_58_; 
v_unused_55_ = lean_ctor_get(v___x_43_, 4);
lean_dec(v_unused_55_);
v_unused_56_ = lean_ctor_get(v___x_43_, 3);
lean_dec(v_unused_56_);
v_unused_57_ = lean_ctor_get(v___x_43_, 2);
lean_dec(v_unused_57_);
v_unused_58_ = lean_ctor_get(v___x_43_, 0);
lean_dec(v_unused_58_);
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_54_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_toAddMonoidWithOne_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_54_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_toOne_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v_toOne_48_ = lean_ctor_get(v_toAddMonoidWithOne_44_, 2);
lean_inc(v_toOne_48_);
lean_dec_ref(v_toAddMonoidWithOne_44_);
lean_inc(v_l_34_);
v___x_49_ = lean_apply_2(v_toAdd_42_, v_toOne_48_, v_l_34_);
v___x_50_ = lean_apply_1(v_toNeg_40_, v___x_49_);
lean_inc_n(v_toZero_37_, 2);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 4, v_toZero_37_);
lean_ctor_set(v___x_46_, 3, v_l_34_);
lean_ctor_set(v___x_46_, 2, v_toZero_37_);
lean_ctor_set(v___x_46_, 1, v___x_50_);
lean_ctor_set(v___x_46_, 0, v_toZero_37_);
v___x_52_ = v___x_46_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_toZero_37_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_toZero_37_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_l_34_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_toZero_37_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_legendreCurve(lean_object* v_R_59_, lean_object* v_inst_60_, lean_object* v_l_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lp_tree_GlobalTheory_legendreCurve___redArg(v_inst_60_, v_l_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_deuringCurve___redArg(lean_object* v_inst_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
lean_object* v_toSemiring_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_75_; 
v_toSemiring_66_ = lean_ctor_get(v_inst_63_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_inst_63_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; lean_object* v_unused_77_; lean_object* v_unused_78_; lean_object* v_unused_79_; 
v_unused_76_ = lean_ctor_get(v_inst_63_, 4);
lean_dec(v_unused_76_);
v_unused_77_ = lean_ctor_get(v_inst_63_, 3);
lean_dec(v_unused_77_);
v_unused_78_ = lean_ctor_get(v_inst_63_, 2);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v_inst_63_, 1);
lean_dec(v_unused_79_);
v___x_68_ = v_inst_63_;
v_isShared_69_ = v_isSharedCheck_75_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_toSemiring_66_);
lean_dec(v_inst_63_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_75_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v_toZero_71_; lean_object* v___x_73_; 
v___x_70_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_66_);
v_toZero_71_ = lean_ctor_get(v___x_70_, 1);
lean_inc_n(v_toZero_71_, 3);
lean_dec_ref(v___x_70_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 4, v_toZero_71_);
lean_ctor_set(v___x_68_, 3, v_toZero_71_);
lean_ctor_set(v___x_68_, 2, v_b_65_);
lean_ctor_set(v___x_68_, 1, v_toZero_71_);
lean_ctor_set(v___x_68_, 0, v_a_64_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_64_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_toZero_71_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_b_65_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v_toZero_71_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v_toZero_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_deuringCurve(lean_object* v_R_80_, lean_object* v_inst_81_, lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_tree_GlobalTheory_deuringCurve___redArg(v_inst_81_, v_a_82_, v_b_83_);
return v___x_84_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
