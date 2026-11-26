// Lean compiler output
// Module: New.UpperBound.Objects.LiftLawsModuloN
// Imports: public import Init public meta import Init public import Lib.ClassField.HeckeCharacter.SplitTameCharacters public import Lib.General.LinearAlgebra.TensorChains
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
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Pi_single___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__2(lean_object*, lean_object*);
static const lean_ctor_object lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___closed__0 = (const lean_object*)&lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0(lean_object* v_N_1_, lean_object* v_i_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_toCommSemiring_6_; lean_object* v___x_7_; lean_object* v_toZero_8_; 
v___x_4_ = lp_mathlib_ZMod_instField___redArg(v_N_1_);
v___x_5_ = lp_mathlib_Field_toSemifield___redArg(v___x_4_);
lean_dec_ref(v___x_4_);
v_toCommSemiring_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref(v_toCommSemiring_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_6_);
v_toZero_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toZero_8_);
lean_dec_ref(v___x_7_);
return v_toZero_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0___boxed(lean_object* v_N_9_, lean_object* v_i_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0(v_N_9_, v_i_10_, v___y_11_);
lean_dec_ref(v_i_10_);
return v_res_12_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1(lean_object* v_inst_13_, lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_17_ = l_instDecidableEqSum_decEq___redArg(v_inst_13_, v___x_16_, v_a_14_, v_b_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1___boxed(lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_b_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1(v_inst_18_, v_a_19_, v_b_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__2(lean_object* v_N_23_, lean_object* v_x_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_toRing_27_; lean_object* v___x_28_; lean_object* v_toAddMonoidWithOne_29_; lean_object* v_toOne_30_; 
v___x_25_ = lp_mathlib_ZMod_instField___redArg(v_N_23_);
v___x_26_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_25_);
v_toRing_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc_ref(v_toRing_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_27_);
v_toAddMonoidWithOne_29_ = lean_ctor_get(v___x_28_, 1);
lean_inc_ref(v_toAddMonoidWithOne_29_);
lean_dec_ref(v___x_28_);
v_toOne_30_ = lean_ctor_get(v_toAddMonoidWithOne_29_, 2);
lean_inc(v_toOne_30_);
lean_dec_ref(v_toAddMonoidWithOne_29_);
return v_toOne_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___redArg(lean_object* v_N_33_, lean_object* v_inst_34_, lean_object* v_j_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_662__overap_41_; lean_object* v___x_42_; 
lean_inc(v_N_33_);
v___f_37_ = lean_alloc_closure((void*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_37_, 0, v_N_33_);
v___f_38_ = lean_alloc_closure((void*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_38_, 0, v_inst_34_);
v___f_39_ = lean_alloc_closure((void*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__2), 2, 1);
lean_closure_set(v___f_39_, 0, v_N_33_);
v___x_40_ = ((lean_object*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___closed__0));
v___x_662__overap_41_ = lp_mathlib_Pi_single___redArg(v___f_37_, v___f_38_, v___x_40_, v___f_39_, v_j_35_);
lean_dec_ref(v___f_39_);
v___x_42_ = lean_apply_1(v___x_662__overap_41_, v_a_36_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector(lean_object* v_E_43_, lean_object* v_n_44_, lean_object* v_inst_45_, lean_object* v_P_46_, lean_object* v_N_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_j_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_700__overap_56_; lean_object* v___x_57_; 
lean_inc(v_N_47_);
v___f_52_ = lean_alloc_closure((void*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_52_, 0, v_N_47_);
v___f_53_ = lean_alloc_closure((void*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_53_, 0, v_inst_49_);
v___f_54_ = lean_alloc_closure((void*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___lam__2), 2, 1);
lean_closure_set(v___f_54_, 0, v_N_47_);
v___x_55_ = ((lean_object*)(lp_GRH_New_IsSplitLevel_lastBasisVector___redArg___closed__0));
v___x_700__overap_56_ = lp_mathlib_Pi_single___redArg(v___f_52_, v___f_53_, v___x_55_, v___f_54_, v_j_50_);
lean_dec_ref(v___f_54_);
v___x_57_ = lean_apply_1(v___x_700__overap_56_, v_a_51_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_IsSplitLevel_lastBasisVector___boxed(lean_object* v_E_58_, lean_object* v_n_59_, lean_object* v_inst_60_, lean_object* v_P_61_, lean_object* v_N_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_j_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_GRH_New_IsSplitLevel_lastBasisVector(v_E_58_, v_n_59_, v_inst_60_, v_P_61_, v_N_62_, v_inst_63_, v_inst_64_, v_j_65_, v_a_66_);
lean_dec(v_P_61_);
lean_dec_ref(v_inst_60_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v_zero_71_; uint8_t v_isZero_72_; 
v_zero_71_ = lean_unsigned_to_nat(0u);
v_isZero_72_ = lean_nat_dec_eq(v_x_68_, v_zero_71_);
if (v_isZero_72_ == 1)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_70_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__1_69_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_69_);
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_x_68_, v_one_75_);
v___x_77_ = lean_apply_1(v_h__2_70_, v_n_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___redArg___boxed(lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___redArg(v_x_78_, v_h__1_79_, v_h__2_80_);
lean_dec(v_x_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter(lean_object* v_motive_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v_zero_86_; uint8_t v_isZero_87_; 
v_zero_86_ = lean_unsigned_to_nat(0u);
v_isZero_87_ = lean_nat_dec_eq(v_x_83_, v_zero_86_);
if (v_isZero_87_ == 1)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_85_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__1_84_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v_one_90_; lean_object* v_n_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_84_);
v_one_90_ = lean_unsigned_to_nat(1u);
v_n_91_ = lean_nat_sub(v_x_83_, v_one_90_);
v___x_92_ = lean_apply_1(v_h__2_85_, v_n_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter___boxed(lean_object* v_motive_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_GRH___private_New_UpperBound_Objects_LiftLawsModuloN_0__New_compUpTo_match__1_splitter(v_motive_93_, v_x_94_, v_h__1_95_, v_h__2_96_);
lean_dec(v_x_94_);
return v_res_97_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_SplitTameCharacters(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_TensorChains(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_LiftLawsModuloN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_HeckeCharacter_SplitTameCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_TensorChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
