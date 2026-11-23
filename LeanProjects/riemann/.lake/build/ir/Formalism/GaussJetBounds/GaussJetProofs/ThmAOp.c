// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Formalism.GaussJetBounds.StatementI public import Formalism.GaussJetBounds.MonoShapeTop
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opInt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opInt(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_00_u03c3_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opInt___boxed(lean_object* v_K_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_00_u03c3_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_DworkPowerSeriesWeights_opInt(v_K_6_, v_inst_7_, v_inst_8_, v_00_u03c3_9_);
lean_dec_ref(v_inst_7_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opA___redArg(lean_object* v_inst_11_, lean_object* v_d_12_, lean_object* v_TT_13_, lean_object* v_T_14_, lean_object* v_s_15_, lean_object* v_i_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_18_, 0, v_d_12_);
lean_inc(v_s_15_);
v___x_19_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_18_, v_s_15_, v_TT_13_);
if (v___x_19_ == 0)
{
goto v___jp_20_;
}
else
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v_i_16_, v___x_30_);
if (v___x_31_ == 0)
{
goto v___jp_20_;
}
else
{
uint8_t v___x_32_; 
lean_dec(v_s_15_);
lean_dec(v_T_14_);
v___x_32_ = lean_nat_dec_eq(v_k_17_, v_i_16_);
lean_dec(v_i_16_);
lean_dec(v_k_17_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_toSemiring_35_; lean_object* v___x_36_; lean_object* v_toZero_37_; 
v___x_33_ = lp_mathlib_Field_toSemifield___redArg(v_inst_11_);
lean_dec_ref(v_inst_11_);
v___x_34_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_33_);
v_toSemiring_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc_ref(v_toSemiring_35_);
lean_dec_ref(v___x_34_);
v___x_36_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_35_);
v_toZero_37_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_toZero_37_);
lean_dec_ref(v___x_36_);
return v_toZero_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_toRing_39_; lean_object* v___x_40_; lean_object* v_toAddMonoidWithOne_41_; lean_object* v_toOne_42_; 
v___x_38_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_11_);
v_toRing_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_toRing_39_);
lean_dec_ref(v___x_38_);
v___x_40_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_39_);
v_toAddMonoidWithOne_41_ = lean_ctor_get(v___x_40_, 1);
lean_inc_ref(v_toAddMonoidWithOne_41_);
lean_dec_ref(v___x_40_);
v_toOne_42_ = lean_ctor_get(v_toAddMonoidWithOne_41_, 2);
lean_inc(v_toOne_42_);
lean_dec_ref(v_toAddMonoidWithOne_41_);
return v_toOne_42_;
}
}
}
v___jp_20_:
{
if (v___x_19_ == 0)
{
lean_object* v___x_21_; 
lean_dec_ref(v_inst_11_);
v___x_21_ = lean_apply_3(v_T_14_, v_s_15_, v_i_16_, v_k_17_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_dec_eq(v_k_17_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec_ref(v_inst_11_);
v___x_24_ = lean_apply_3(v_T_14_, v_s_15_, v_i_16_, v_k_17_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_toSemiring_27_; lean_object* v___x_28_; lean_object* v_toZero_29_; 
lean_dec(v_k_17_);
lean_dec(v_i_16_);
lean_dec(v_s_15_);
lean_dec(v_T_14_);
v___x_25_ = lp_mathlib_Field_toSemifield___redArg(v_inst_11_);
lean_dec_ref(v_inst_11_);
v___x_26_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_25_);
v_toSemiring_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc_ref(v_toSemiring_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_27_);
v_toZero_29_ = lean_ctor_get(v___x_28_, 1);
lean_inc(v_toZero_29_);
lean_dec_ref(v___x_28_);
return v_toZero_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opA(lean_object* v_K_43_, lean_object* v_inst_44_, lean_object* v_d_45_, lean_object* v_N0_46_, lean_object* v_TT_47_, lean_object* v_T_48_, lean_object* v_s_49_, lean_object* v_i_50_, lean_object* v_k_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_tree_Formalism_DworkPowerSeriesWeights_opA___redArg(v_inst_44_, v_d_45_, v_TT_47_, v_T_48_, v_s_49_, v_i_50_, v_k_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_opA___boxed(lean_object* v_K_53_, lean_object* v_inst_54_, lean_object* v_d_55_, lean_object* v_N0_56_, lean_object* v_TT_57_, lean_object* v_T_58_, lean_object* v_s_59_, lean_object* v_i_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_DworkPowerSeriesWeights_opA(v_K_53_, v_inst_54_, v_d_55_, v_N0_56_, v_TT_57_, v_T_58_, v_s_59_, v_i_60_, v_k_61_);
lean_dec(v_N0_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___redArg___lam__0(lean_object* v_00_u03ba_63_, lean_object* v_k_64_, lean_object* v_s_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_toFun_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_76_; 
v_toFun_67_ = lean_ctor_get(v_00_u03ba_63_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_00_u03ba_63_);
if (v_isSharedCheck_76_ == 0)
{
lean_object* v_unused_77_; 
v_unused_77_ = lean_ctor_get(v_00_u03ba_63_, 0);
lean_dec(v_unused_77_);
v___x_69_ = v_00_u03ba_63_;
v_isShared_70_ = v_isSharedCheck_76_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_toFun_67_);
lean_dec(v_00_u03ba_63_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_76_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v_b_66_);
lean_ctor_set(v___x_69_, 0, v_k_64_);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_b_66_);
v___x_72_ = v_reuseFailAlloc_75_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_s_65_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_apply_1(v_toFun_67_, v___x_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___redArg(lean_object* v_N1_78_, lean_object* v_s_79_, lean_object* v_k_80_, lean_object* v_00_u03ba_81_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___f_82_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___redArg___lam__0), 4, 3);
lean_closure_set(v___f_82_, 0, v_00_u03ba_81_);
lean_closure_set(v___f_82_, 1, v_k_80_);
lean_closure_set(v___f_82_, 2, v_s_79_);
v___x_83_ = l_List_finRange(v_N1_78_);
v___x_84_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_83_, v___f_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg(lean_object* v_d_85_, lean_object* v_N0_86_, lean_object* v_N1_87_, lean_object* v_s_88_, lean_object* v_k_89_, lean_object* v_00_u03ba_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___redArg(v_N1_87_, v_s_88_, v_k_89_, v_00_u03ba_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg___boxed(lean_object* v_d_92_, lean_object* v_N0_93_, lean_object* v_N1_94_, lean_object* v_s_95_, lean_object* v_k_96_, lean_object* v_00_u03ba_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_DworkPowerSeriesWeights_rowDeg(v_d_92_, v_N0_93_, v_N1_94_, v_s_95_, v_k_96_, v_00_u03ba_97_);
lean_dec(v_N0_93_);
lean_dec(v_d_92_);
return v_res_98_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementI(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_MonoShapeTop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GenLogInverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_MonoShapeTop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
