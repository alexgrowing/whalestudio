// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.RootLemma
// Imports: public import Init public meta import Init public import New.UpperBound.ElementaryDivisors.TwistingData
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
lean_object* lp_GRH_New_FrobeniusCycle_rootVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_swap___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_swap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_GRH_New_transvectionGL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toHasDistribNeg___redArg(lean_object*);
lean_object* lp_mathlib_Function_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_diagGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rootSL___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_rootSL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rootSL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rootSL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varX___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varX___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varY___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varY(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varY___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_merge___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_merge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_merge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_poleOrder___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_poleOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_poleOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_crossSign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_crossSign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_crossSign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_adicFiltration___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration(lean_object* v_R_5_, lean_object* v_inst_6_, lean_object* v_w_7_, lean_object* v_t_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_adicFiltration___boxed(lean_object* v_R_10_, lean_object* v_inst_11_, lean_object* v_w_12_, lean_object* v_t_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_adicFiltration(v_R_10_, v_inst_11_, v_w_12_, v_t_13_);
lean_dec(v_t_13_);
lean_dec(v_w_12_);
lean_dec_ref(v_inst_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration___redArg(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_gaussFiltration___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration(lean_object* v_00_u03c3_19_, lean_object* v_R_20_, lean_object* v_inst_21_, lean_object* v_F_22_, lean_object* v_c_23_, lean_object* v_t_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gaussFiltration___boxed(lean_object* v_00_u03c3_26_, lean_object* v_R_27_, lean_object* v_inst_28_, lean_object* v_F_29_, lean_object* v_c_30_, lean_object* v_t_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_gaussFiltration(v_00_u03c3_26_, v_R_27_, v_inst_28_, v_F_29_, v_c_30_, v_t_31_);
lean_dec(v_t_31_);
lean_dec(v_c_30_);
lean_dec_ref(v_F_29_);
lean_dec_ref(v_inst_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootSL___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootSL___redArg___boxed(lean_object* v___dummy_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_rootSL___redArg();
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootSL(lean_object* v_k_37_, lean_object* v_W_38_, lean_object* v_inst_39_, lean_object* v_a_40_, lean_object* v_a_x27_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootSL___boxed(lean_object* v_k_43_, lean_object* v_W_44_, lean_object* v_inst_45_, lean_object* v_a_46_, lean_object* v_a_x27_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_rootSL(v_k_43_, v_W_44_, v_inst_45_, v_a_46_, v_a_x27_47_);
lean_dec(v_a_x27_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_inst_45_);
lean_dec(v_k_43_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varX___redArg(lean_object* v_T_49_, lean_object* v_D_50_, lean_object* v_s_51_){
_start:
{
lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_54_; 
v_fst_52_ = lean_ctor_get(v_D_50_, 1);
lean_inc(v_fst_52_);
v_snd_53_ = lean_ctor_get(v_D_50_, 2);
lean_inc(v_snd_53_);
lean_dec_ref(v_D_50_);
v___x_54_ = lp_GRH_New_FrobeniusCycle_rootVar___redArg(v_T_49_, v_snd_53_, v_fst_52_, v_s_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varX(lean_object* v_R_55_, lean_object* v_N_56_, lean_object* v_k_57_, lean_object* v_W_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_T_62_, lean_object* v_D_63_, lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_GRH_New_FrobeniusCycle_RootAt_varX___redArg(v_T_62_, v_D_63_, v_s_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varX___boxed(lean_object* v_R_66_, lean_object* v_N_67_, lean_object* v_k_68_, lean_object* v_W_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_T_73_, lean_object* v_D_74_, lean_object* v_s_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_FrobeniusCycle_RootAt_varX(v_R_66_, v_N_67_, v_k_68_, v_W_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_T_73_, v_D_74_, v_s_75_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
lean_dec(v_k_68_);
lean_dec(v_N_67_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varY___redArg(lean_object* v_T_77_, lean_object* v_D_78_, lean_object* v_s_79_){
_start:
{
lean_object* v_fst_80_; lean_object* v_snd_81_; lean_object* v___x_82_; 
v_fst_80_ = lean_ctor_get(v_D_78_, 1);
lean_inc(v_fst_80_);
v_snd_81_ = lean_ctor_get(v_D_78_, 2);
lean_inc(v_snd_81_);
lean_dec_ref(v_D_78_);
v___x_82_ = lp_GRH_New_FrobeniusCycle_rootVar___redArg(v_T_77_, v_fst_80_, v_snd_81_, v_s_79_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varY(lean_object* v_R_83_, lean_object* v_N_84_, lean_object* v_k_85_, lean_object* v_W_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_T_90_, lean_object* v_D_91_, lean_object* v_s_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_GRH_New_FrobeniusCycle_RootAt_varY___redArg(v_T_90_, v_D_91_, v_s_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_varY___boxed(lean_object* v_R_94_, lean_object* v_N_95_, lean_object* v_k_96_, lean_object* v_W_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_T_101_, lean_object* v_D_102_, lean_object* v_s_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_GRH_New_FrobeniusCycle_RootAt_varY(v_R_94_, v_N_95_, v_k_96_, v_W_97_, v_inst_98_, v_inst_99_, v_inst_100_, v_T_101_, v_D_102_, v_s_103_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
lean_dec(v_k_96_);
lean_dec(v_N_95_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapVar___redArg(lean_object* v_k_105_, lean_object* v_D_106_, lean_object* v_z_107_){
_start:
{
lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
v_fst_108_ = lean_ctor_get(v_D_106_, 1);
lean_inc(v_fst_108_);
v_snd_109_ = lean_ctor_get(v_D_106_, 2);
lean_inc(v_snd_109_);
lean_dec_ref(v_D_106_);
v_fst_110_ = lean_ctor_get(v_z_107_, 0);
v_snd_111_ = lean_ctor_get(v_z_107_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_z_107_);
if (v_isSharedCheck_122_ == 0)
{
v___x_113_ = v_z_107_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_inc(v_fst_110_);
lean_dec(v_z_107_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_toFun_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_115_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_115_, 0, v_k_105_);
v___x_116_ = lp_mathlib_Equiv_swap___redArg(v___x_115_, v_fst_108_, v_snd_109_);
v_toFun_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_toFun_117_);
lean_dec_ref(v___x_116_);
v___x_118_ = lean_apply_1(v_toFun_117_, v_fst_110_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_118_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_snd_111_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapVar(lean_object* v_R_123_, lean_object* v_N_124_, lean_object* v_k_125_, lean_object* v_W_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_T_130_, lean_object* v_D_131_, lean_object* v_z_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lp_GRH_New_FrobeniusCycle_RootAt_swapVar___redArg(v_k_125_, v_D_131_, v_z_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapVar___boxed(lean_object* v_R_134_, lean_object* v_N_135_, lean_object* v_k_136_, lean_object* v_W_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_T_141_, lean_object* v_D_142_, lean_object* v_z_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_GRH_New_FrobeniusCycle_RootAt_swapVar(v_R_134_, v_N_135_, v_k_136_, v_W_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_T_141_, v_D_142_, v_z_143_);
lean_dec_ref(v_T_141_);
lean_dec_ref(v_inst_139_);
lean_dec_ref(v_inst_138_);
lean_dec(v_N_135_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_merge___redArg(lean_object* v_N_145_, lean_object* v_k_146_, lean_object* v_T_147_, lean_object* v_D_148_, lean_object* v_z_149_){
_start:
{
lean_object* v_letter_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_letter_150_ = lean_ctor_get(v_D_148_, 0);
lean_inc_n(v_letter_150_, 2);
v___x_151_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_151_, 0, v_k_146_);
v___x_152_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_152_, 0, v_N_145_);
lean_inc_ref(v_D_148_);
lean_inc_ref(v_T_147_);
v___x_153_ = lp_GRH_New_FrobeniusCycle_RootAt_varY___redArg(v_T_147_, v_D_148_, v_letter_150_);
lean_inc_ref(v_z_149_);
v___x_154_ = l_instDecidableEqProd___redArg(v___x_151_, v___x_152_, v_z_149_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_letter_150_);
lean_dec_ref(v_D_148_);
lean_dec_ref(v_T_147_);
return v_z_149_;
}
else
{
lean_object* v___x_155_; 
lean_dec_ref(v_z_149_);
v___x_155_ = lp_GRH_New_FrobeniusCycle_RootAt_varX___redArg(v_T_147_, v_D_148_, v_letter_150_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_merge(lean_object* v_R_156_, lean_object* v_N_157_, lean_object* v_k_158_, lean_object* v_W_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_T_163_, lean_object* v_D_164_, lean_object* v_z_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lp_GRH_New_FrobeniusCycle_RootAt_merge___redArg(v_N_157_, v_k_158_, v_T_163_, v_D_164_, v_z_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_merge___boxed(lean_object* v_R_167_, lean_object* v_N_168_, lean_object* v_k_169_, lean_object* v_W_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_T_174_, lean_object* v_D_175_, lean_object* v_z_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = lp_GRH_New_FrobeniusCycle_RootAt_merge(v_R_167_, v_N_168_, v_k_169_, v_W_170_, v_inst_171_, v_inst_172_, v_inst_173_, v_T_174_, v_D_175_, v_z_176_);
lean_dec_ref(v_inst_172_);
lean_dec_ref(v_inst_171_);
return v_res_177_;
}
}
static lean_object* _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_to_int(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0, &lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0_once, _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0);
v___x_181_ = lean_int_neg(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__2(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg(lean_object* v_N_184_, lean_object* v_k_185_, lean_object* v_T_186_, lean_object* v_D_187_, lean_object* v_z_188_){
_start:
{
uint8_t v___y_192_; lean_object* v_snd_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_snd_194_ = lean_ctor_get(v_z_188_, 1);
lean_inc_n(v_snd_194_, 2);
v___x_195_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_195_, 0, v_k_185_);
v___x_196_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_196_, 0, v_N_184_);
lean_inc_ref(v_D_187_);
lean_inc_ref(v_T_186_);
v___x_197_ = lp_GRH_New_FrobeniusCycle_RootAt_varY___redArg(v_T_186_, v_D_187_, v_snd_194_);
v___x_198_ = l_instDecidableEqProd___redArg(v___x_195_, v___x_196_, v_z_188_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec(v_snd_194_);
lean_dec_ref(v_D_187_);
lean_dec_ref(v_T_186_);
v___x_199_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__2, &lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__2_once, _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__2);
return v___x_199_;
}
else
{
lean_object* v_isEven_200_; lean_object* v_letter_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_isEven_200_ = lean_ctor_get(v_T_186_, 3);
lean_inc_ref_n(v_isEven_200_, 2);
lean_dec_ref(v_T_186_);
v_letter_201_ = lean_ctor_get(v_D_187_, 0);
lean_inc(v_letter_201_);
lean_dec_ref(v_D_187_);
v___x_202_ = lean_apply_1(v_isEven_200_, v_snd_194_);
v___x_203_ = lean_apply_1(v_isEven_200_, v_letter_201_);
v___x_204_ = lean_unbox(v___x_203_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = lean_unbox(v___x_202_);
if (v___x_205_ == 0)
{
v___y_192_ = v___x_198_;
goto v___jp_191_;
}
else
{
goto v___jp_189_;
}
}
else
{
uint8_t v___x_206_; 
v___x_206_ = lean_unbox(v___x_202_);
v___y_192_ = v___x_206_;
goto v___jp_191_;
}
}
v___jp_189_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0, &lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0_once, _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0);
return v___x_190_;
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
goto v___jp_189_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1, &lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1_once, _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign(lean_object* v_R_207_, lean_object* v_N_208_, lean_object* v_k_209_, lean_object* v_W_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_T_214_, lean_object* v_D_215_, lean_object* v_z_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg(v_N_208_, v_k_209_, v_T_214_, v_D_215_, v_z_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_sign___boxed(lean_object* v_R_218_, lean_object* v_N_219_, lean_object* v_k_220_, lean_object* v_W_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_T_225_, lean_object* v_D_226_, lean_object* v_z_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_GRH_New_FrobeniusCycle_RootAt_sign(v_R_218_, v_N_219_, v_k_220_, v_W_221_, v_inst_222_, v_inst_223_, v_inst_224_, v_T_225_, v_D_226_, v_z_227_);
lean_dec_ref(v_inst_223_);
lean_dec_ref(v_inst_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card___redArg(lean_object* v_N_229_, lean_object* v_T_230_){
_start:
{
lean_object* v_p_231_; lean_object* v_frobExp_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_p_231_ = lean_ctor_get(v_T_230_, 0);
v_frobExp_232_ = lean_ctor_get(v_T_230_, 1);
v___x_233_ = lean_nat_pow(v_p_231_, v_frobExp_232_);
v___x_234_ = lean_nat_pow(v___x_233_, v_N_229_);
lean_dec(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card___redArg___boxed(lean_object* v_N_235_, lean_object* v_T_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_GRH_New_FrobeniusCycle_RootAt_card___redArg(v_N_235_, v_T_236_);
lean_dec_ref(v_T_236_);
lean_dec(v_N_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card(lean_object* v_R_238_, lean_object* v_N_239_, lean_object* v_k_240_, lean_object* v_W_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_T_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lp_GRH_New_FrobeniusCycle_RootAt_card___redArg(v_N_239_, v_T_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_card___boxed(lean_object* v_R_248_, lean_object* v_N_249_, lean_object* v_k_250_, lean_object* v_W_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_T_255_, lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = lp_GRH_New_FrobeniusCycle_RootAt_card(v_R_248_, v_N_249_, v_k_250_, v_W_251_, v_inst_252_, v_inst_253_, v_inst_254_, v_T_255_, v_x_256_);
lean_dec_ref(v_x_256_);
lean_dec_ref(v_T_255_);
lean_dec_ref(v_inst_253_);
lean_dec_ref(v_inst_252_);
lean_dec(v_k_250_);
lean_dec(v_N_249_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg(lean_object* v_N_258_, lean_object* v_T_259_, lean_object* v_D_260_, lean_object* v_s_261_){
_start:
{
lean_object* v_p_262_; lean_object* v_frobExp_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_toSub_267_; lean_object* v_letter_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_p_262_ = lean_ctor_get(v_T_259_, 0);
v_frobExp_263_ = lean_ctor_get(v_T_259_, 1);
lean_inc(v_N_258_);
v___x_264_ = lp_mathlib_ZMod_commRing(v_N_258_);
v___x_265_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_264_);
v___x_266_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_265_);
lean_dec_ref(v___x_265_);
v_toSub_267_ = lean_ctor_get(v___x_266_, 2);
lean_inc(v_toSub_267_);
lean_dec_ref(v___x_266_);
v_letter_268_ = lean_ctor_get(v_D_260_, 0);
lean_inc(v_letter_268_);
lean_dec_ref(v_D_260_);
v___x_269_ = lean_nat_pow(v_p_262_, v_frobExp_263_);
v___x_270_ = lean_apply_2(v_toSub_267_, v_s_261_, v_letter_268_);
v___x_271_ = lp_mathlib_ZMod_val(v_N_258_, v___x_270_);
lean_dec(v___x_270_);
lean_dec(v_N_258_);
v___x_272_ = lean_nat_pow(v___x_269_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_269_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg___boxed(lean_object* v_N_273_, lean_object* v_T_274_, lean_object* v_D_275_, lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg(v_N_273_, v_T_274_, v_D_275_, v_s_276_);
lean_dec_ref(v_T_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower(lean_object* v_R_278_, lean_object* v_N_279_, lean_object* v_k_280_, lean_object* v_W_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_T_285_, lean_object* v_D_286_, lean_object* v_s_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg(v_N_279_, v_T_285_, v_D_286_, v_s_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_frobPower___boxed(lean_object* v_R_289_, lean_object* v_N_290_, lean_object* v_k_291_, lean_object* v_W_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_T_296_, lean_object* v_D_297_, lean_object* v_s_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = lp_GRH_New_FrobeniusCycle_RootAt_frobPower(v_R_289_, v_N_290_, v_k_291_, v_W_292_, v_inst_293_, v_inst_294_, v_inst_295_, v_T_296_, v_D_297_, v_s_298_);
lean_dec_ref(v_T_296_);
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
lean_dec(v_k_291_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_poleOrder___redArg(lean_object* v_N_300_, lean_object* v_k_301_, lean_object* v_T_302_, lean_object* v_D_303_, lean_object* v_z_304_){
_start:
{
lean_object* v_snd_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_snd_305_ = lean_ctor_get(v_z_304_, 1);
lean_inc_n(v_snd_305_, 2);
v___x_306_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_306_, 0, v_k_301_);
lean_inc(v_N_300_);
v___x_307_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_307_, 0, v_N_300_);
lean_inc_ref(v_D_303_);
lean_inc_ref(v_T_302_);
v___x_308_ = lp_GRH_New_FrobeniusCycle_RootAt_varX___redArg(v_T_302_, v_D_303_, v_snd_305_);
v___x_309_ = l_instDecidableEqProd___redArg(v___x_306_, v___x_307_, v_z_304_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
lean_dec(v_snd_305_);
lean_dec_ref(v_D_303_);
lean_dec_ref(v_T_302_);
lean_dec(v_N_300_);
v___x_310_ = lean_unsigned_to_nat(0u);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lp_GRH_New_FrobeniusCycle_RootAt_card___redArg(v_N_300_, v_T_302_);
v___x_312_ = lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg(v_N_300_, v_T_302_, v_D_303_, v_snd_305_);
lean_dec_ref(v_T_302_);
v___x_313_ = lean_nat_mul(v___x_311_, v___x_312_);
lean_dec(v___x_312_);
lean_dec(v___x_311_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_poleOrder(lean_object* v_R_314_, lean_object* v_N_315_, lean_object* v_k_316_, lean_object* v_W_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_T_321_, lean_object* v_D_322_, lean_object* v_z_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lp_GRH_New_FrobeniusCycle_RootAt_poleOrder___redArg(v_N_315_, v_k_316_, v_T_321_, v_D_322_, v_z_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_poleOrder___boxed(lean_object* v_R_325_, lean_object* v_N_326_, lean_object* v_k_327_, lean_object* v_W_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_T_332_, lean_object* v_D_333_, lean_object* v_z_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = lp_GRH_New_FrobeniusCycle_RootAt_poleOrder(v_R_325_, v_N_326_, v_k_327_, v_W_328_, v_inst_329_, v_inst_330_, v_inst_331_, v_T_332_, v_D_333_, v_z_334_);
lean_dec_ref(v_inst_330_);
lean_dec_ref(v_inst_329_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder___redArg(lean_object* v_N_336_, lean_object* v_k_337_, lean_object* v_T_338_, lean_object* v_D_339_, lean_object* v_z_340_){
_start:
{
lean_object* v_snd_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_snd_341_ = lean_ctor_get(v_z_340_, 1);
lean_inc_n(v_snd_341_, 2);
v___x_342_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_342_, 0, v_k_337_);
lean_inc(v_N_336_);
v___x_343_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_343_, 0, v_N_336_);
lean_inc_ref(v_D_339_);
lean_inc_ref(v_T_338_);
v___x_344_ = lp_GRH_New_FrobeniusCycle_RootAt_varY___redArg(v_T_338_, v_D_339_, v_snd_341_);
v___x_345_ = l_instDecidableEqProd___redArg(v___x_342_, v___x_343_, v_z_340_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
lean_dec(v_snd_341_);
lean_dec_ref(v_D_339_);
lean_dec_ref(v_T_338_);
lean_dec(v_N_336_);
v___x_346_ = lean_unsigned_to_nat(0u);
return v___x_346_;
}
else
{
lean_object* v_letter_347_; uint8_t v___x_348_; 
v_letter_347_ = lean_ctor_get(v_D_339_, 0);
v___x_348_ = lp_mathlib_ZMod_decidableEq(v_N_336_, v_snd_341_, v_letter_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lp_GRH_New_FrobeniusCycle_RootAt_frobPower___redArg(v_N_336_, v_T_338_, v_D_339_, v_snd_341_);
lean_dec_ref(v_T_338_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
lean_dec(v_snd_341_);
lean_dec_ref(v_D_339_);
v___x_350_ = lp_GRH_New_FrobeniusCycle_RootAt_card___redArg(v_N_336_, v_T_338_);
lean_dec_ref(v_T_338_);
lean_dec(v_N_336_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder(lean_object* v_R_351_, lean_object* v_N_352_, lean_object* v_k_353_, lean_object* v_W_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_T_358_, lean_object* v_D_359_, lean_object* v_z_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder___redArg(v_N_352_, v_k_353_, v_T_358_, v_D_359_, v_z_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder___boxed(lean_object* v_R_362_, lean_object* v_N_363_, lean_object* v_k_364_, lean_object* v_W_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_T_369_, lean_object* v_D_370_, lean_object* v_z_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = lp_GRH_New_FrobeniusCycle_RootAt_zeroOrder(v_R_362_, v_N_363_, v_k_364_, v_W_365_, v_inst_366_, v_inst_367_, v_inst_368_, v_T_369_, v_D_370_, v_z_371_);
lean_dec_ref(v_inst_367_);
lean_dec_ref(v_inst_366_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_crossSign___redArg(lean_object* v_N_373_, lean_object* v_k_374_, lean_object* v_inst_375_, lean_object* v_T_376_, lean_object* v_D_377_, lean_object* v_z_378_){
_start:
{
lean_object* v_snd_379_; lean_object* v_letter_380_; lean_object* v_toSemiring_381_; lean_object* v___x_382_; lean_object* v_toAdd_383_; lean_object* v___x_384_; lean_object* v_toIntCast_385_; lean_object* v___x_386_; lean_object* v_toZero_387_; uint8_t v___x_388_; 
v_snd_379_ = lean_ctor_get(v_z_378_, 1);
v_letter_380_ = lean_ctor_get(v_D_377_, 0);
v_toSemiring_381_ = lean_ctor_get(v_inst_375_, 0);
lean_inc_ref_n(v_toSemiring_381_, 2);
v___x_382_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_381_);
v_toAdd_383_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_toAdd_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_375_);
v_toIntCast_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_toIntCast_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_381_);
v_toZero_387_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_toZero_387_);
lean_dec_ref(v___x_386_);
v___x_388_ = lp_mathlib_ZMod_decidableEq(v_N_373_, v_snd_379_, v_letter_380_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_toZero_387_);
lean_inc_ref(v_z_378_);
lean_inc_ref_n(v_D_377_, 2);
lean_inc_ref(v_T_376_);
lean_inc_n(v_k_374_, 2);
lean_inc(v_N_373_);
v___x_389_ = lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg(v_N_373_, v_k_374_, v_T_376_, v_D_377_, v_z_378_);
lean_inc(v_toIntCast_385_);
v___x_390_ = lean_apply_1(v_toIntCast_385_, v___x_389_);
v___x_391_ = lp_GRH_New_FrobeniusCycle_RootAt_swapVar___redArg(v_k_374_, v_D_377_, v_z_378_);
v___x_392_ = lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg(v_N_373_, v_k_374_, v_T_376_, v_D_377_, v___x_391_);
v___x_393_ = lean_apply_1(v_toIntCast_385_, v___x_392_);
v___x_394_ = lean_apply_2(v_toAdd_383_, v___x_390_, v___x_393_);
return v___x_394_;
}
else
{
lean_dec(v_toIntCast_385_);
lean_dec(v_toAdd_383_);
lean_dec_ref(v_z_378_);
lean_dec_ref(v_D_377_);
lean_dec_ref(v_T_376_);
lean_dec(v_k_374_);
lean_dec(v_N_373_);
return v_toZero_387_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_crossSign(lean_object* v_R_395_, lean_object* v_N_396_, lean_object* v_k_397_, lean_object* v_W_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_T_402_, lean_object* v_D_403_, lean_object* v_z_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lp_GRH_New_FrobeniusCycle_RootAt_crossSign___redArg(v_N_396_, v_k_397_, v_inst_399_, v_T_402_, v_D_403_, v_z_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_crossSign___boxed(lean_object* v_R_406_, lean_object* v_N_407_, lean_object* v_k_408_, lean_object* v_W_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_T_413_, lean_object* v_D_414_, lean_object* v_z_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = lp_GRH_New_FrobeniusCycle_RootAt_crossSign(v_R_406_, v_N_407_, v_k_408_, v_W_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_T_413_, v_D_414_, v_z_415_);
lean_dec_ref(v_inst_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__0(lean_object* v_toMonoid_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_toOne_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v___x_419_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_417_);
v___x_420_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_419_);
v_toOne_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v___x_420_, 1);
lean_dec(v_unused_429_);
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_toOne_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
lean_inc(v_toOne_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_toOne_421_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_toOne_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_toOne_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__0___boxed(lean_object* v_toMonoid_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__0(v_toMonoid_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_toMonoid_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__1(lean_object* v_inv_433_, lean_object* v___y_434_, lean_object* v_j_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_apply_2(v_inv_433_, v_j_435_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__2(lean_object* v_inv_437_, lean_object* v_j_438_, lean_object* v_j_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_apply_2(v_inv_437_, v_j_438_, v_j_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__3(lean_object* v_inv_441_, lean_object* v___x_442_, lean_object* v_toMul_443_, lean_object* v_toAddCommMonoid_444_, lean_object* v___f_445_, lean_object* v_j_446_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_448_; 
v___f_447_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__2), 3, 2);
lean_closure_set(v___f_447_, 0, v_inv_441_);
lean_closure_set(v___f_447_, 1, v_j_446_);
v___x_448_ = lp_mathlib_dotProduct___redArg(v___x_442_, v_toMul_443_, v_toAddCommMonoid_444_, v___f_447_, v___f_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__3___boxed(lean_object* v_inv_449_, lean_object* v___x_450_, lean_object* v_toMul_451_, lean_object* v_toAddCommMonoid_452_, lean_object* v___f_453_, lean_object* v_j_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__3(v_inv_449_, v___x_450_, v_toMul_451_, v_toAddCommMonoid_452_, v___f_453_, v_j_454_);
lean_dec_ref(v_toAddCommMonoid_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__4(lean_object* v_inv_456_, lean_object* v___y_457_, lean_object* v_j_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_apply_2(v_inv_456_, v___y_457_, v_j_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__5(lean_object* v_inv_460_, lean_object* v_inv_461_, lean_object* v___x_462_, lean_object* v_toMul_463_, lean_object* v_toAddCommMonoid_464_, lean_object* v_inv_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___f_469_; lean_object* v___f_470_; lean_object* v___x_471_; 
v___f_468_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__1), 3, 2);
lean_closure_set(v___f_468_, 0, v_inv_460_);
lean_closure_set(v___f_468_, 1, v___y_467_);
lean_inc_ref(v_toAddCommMonoid_464_);
lean_inc(v_toMul_463_);
lean_inc(v___x_462_);
v___f_469_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_469_, 0, v_inv_461_);
lean_closure_set(v___f_469_, 1, v___x_462_);
lean_closure_set(v___f_469_, 2, v_toMul_463_);
lean_closure_set(v___f_469_, 3, v_toAddCommMonoid_464_);
lean_closure_set(v___f_469_, 4, v___f_468_);
v___f_470_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__4), 3, 2);
lean_closure_set(v___f_470_, 0, v_inv_465_);
lean_closure_set(v___f_470_, 1, v___y_466_);
v___x_471_ = lp_mathlib_dotProduct___redArg(v___x_462_, v_toMul_463_, v_toAddCommMonoid_464_, v___f_470_, v___f_469_);
lean_dec_ref(v_toAddCommMonoid_464_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__6(lean_object* v_val_472_, lean_object* v___y_473_, lean_object* v_j_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_apply_2(v_val_472_, v_j_474_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__7(lean_object* v_val_476_, lean_object* v___y_477_, lean_object* v_j_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = lean_apply_2(v_val_476_, v___y_477_, v_j_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__8(lean_object* v_val_480_, lean_object* v_j_481_, lean_object* v_j_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_apply_2(v_val_480_, v_j_482_, v_j_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__9(lean_object* v_val_484_, lean_object* v___x_485_, lean_object* v_toMul_486_, lean_object* v_toAddCommMonoid_487_, lean_object* v___f_488_, lean_object* v_j_489_){
_start:
{
lean_object* v___f_490_; lean_object* v___x_491_; 
v___f_490_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__8), 3, 2);
lean_closure_set(v___f_490_, 0, v_val_484_);
lean_closure_set(v___f_490_, 1, v_j_489_);
v___x_491_ = lp_mathlib_dotProduct___redArg(v___x_485_, v_toMul_486_, v_toAddCommMonoid_487_, v___f_488_, v___f_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__9___boxed(lean_object* v_val_492_, lean_object* v___x_493_, lean_object* v_toMul_494_, lean_object* v_toAddCommMonoid_495_, lean_object* v___f_496_, lean_object* v_j_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__9(v_val_492_, v___x_493_, v_toMul_494_, v_toAddCommMonoid_495_, v___f_496_, v_j_497_);
lean_dec_ref(v_toAddCommMonoid_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__10(lean_object* v_val_499_, lean_object* v_val_500_, lean_object* v_val_501_, lean_object* v___x_502_, lean_object* v_toMul_503_, lean_object* v_toAddCommMonoid_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v___f_507_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__6), 3, 2);
lean_closure_set(v___f_507_, 0, v_val_499_);
lean_closure_set(v___f_507_, 1, v___y_506_);
v___f_508_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__7), 3, 2);
lean_closure_set(v___f_508_, 0, v_val_500_);
lean_closure_set(v___f_508_, 1, v___y_505_);
lean_inc_ref(v_toAddCommMonoid_504_);
lean_inc(v_toMul_503_);
lean_inc(v___x_502_);
v___f_509_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_509_, 0, v_val_501_);
lean_closure_set(v___f_509_, 1, v___x_502_);
lean_closure_set(v___f_509_, 2, v_toMul_503_);
lean_closure_set(v___f_509_, 3, v_toAddCommMonoid_504_);
lean_closure_set(v___f_509_, 4, v___f_508_);
v___x_510_ = lp_mathlib_dotProduct___redArg(v___x_502_, v_toMul_503_, v_toAddCommMonoid_504_, v___f_509_, v___f_507_);
lean_dec_ref(v_toAddCommMonoid_504_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg(lean_object* v_k_511_, lean_object* v_inst_512_, lean_object* v_T_513_, lean_object* v_D_514_, lean_object* v_r_515_){
_start:
{
lean_object* v_toSemiring_516_; lean_object* v_letter_517_; lean_object* v_fst_518_; lean_object* v_snd_519_; lean_object* v_isEven_520_; lean_object* v_toMonoid_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_toNeg_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___y_532_; uint8_t v___x_568_; 
v_toSemiring_516_ = lean_ctor_get(v_inst_512_, 0);
v_letter_517_ = lean_ctor_get(v_D_514_, 0);
lean_inc(v_letter_517_);
v_fst_518_ = lean_ctor_get(v_D_514_, 1);
lean_inc_n(v_fst_518_, 2);
v_snd_519_ = lean_ctor_get(v_D_514_, 2);
lean_inc_n(v_snd_519_, 2);
lean_dec_ref(v_D_514_);
v_isEven_520_ = lean_ctor_get(v_T_513_, 3);
lean_inc_ref(v_isEven_520_);
lean_dec_ref(v_T_513_);
v_toMonoid_521_ = lean_ctor_get(v_toSemiring_516_, 1);
v___x_522_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_512_);
v___x_523_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_512_);
v___x_524_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_523_);
lean_dec_ref(v___x_523_);
v_toNeg_525_ = lean_ctor_get(v___x_524_, 1);
lean_inc(v_toNeg_525_);
lean_dec_ref(v___x_524_);
lean_inc(v_k_511_);
v___x_526_ = l_List_finRange(v_k_511_);
v___x_527_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_527_, 0, v_k_511_);
lean_inc_ref(v___x_527_);
lean_inc_ref(v_inst_512_);
v___x_528_ = lp_mathlib_Matrix_GeneralLinearGroup_swap___redArg(v_inst_512_, v___x_527_, v_fst_518_, v_snd_519_);
v___x_529_ = lean_apply_1(v_isEven_520_, v_letter_517_);
lean_inc_ref(v_toMonoid_521_);
v___f_530_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_530_, 0, v_toMonoid_521_);
v___x_568_ = lean_unbox(v___x_529_);
if (v___x_568_ == 0)
{
lean_dec(v_toNeg_525_);
v___y_532_ = v_r_515_;
goto v___jp_531_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_apply_1(v_toNeg_525_, v_r_515_);
v___y_532_ = v___x_569_;
goto v___jp_531_;
}
v___jp_531_:
{
lean_object* v_val_533_; lean_object* v_inv_534_; lean_object* v___x_535_; lean_object* v_val_536_; lean_object* v_inv_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_567_; 
v_val_533_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_533_);
v_inv_534_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_inv_534_);
lean_dec_ref(v___x_528_);
lean_inc(v_fst_518_);
lean_inc_ref(v_inst_512_);
lean_inc_ref(v___x_527_);
v___x_535_ = lp_GRH_New_transvectionGL___redArg(v___x_527_, v_inst_512_, v_fst_518_, v_snd_519_, v___y_532_);
v_val_536_ = lean_ctor_get(v___x_535_, 0);
v_inv_537_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_567_ == 0)
{
v___x_539_ = v___x_535_;
v_isShared_540_ = v_isSharedCheck_567_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_inv_537_);
lean_inc(v_val_536_);
lean_dec(v___x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_567_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v_toAddCommMonoid_542_; lean_object* v___x_543_; lean_object* v_toMul_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_toOne_547_; lean_object* v___x_167__overap_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_541_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_516_);
v_toAddCommMonoid_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_toAddCommMonoid_542_);
v___x_543_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_541_);
v_toMul_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_toMul_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_521_);
v___x_546_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_545_);
v_toOne_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_toOne_547_);
lean_dec_ref(v___x_546_);
v___x_167__overap_548_ = lp_mathlib_NonUnitalNonAssocRing_toHasDistribNeg___redArg(v___x_522_);
lean_dec_ref(v___x_522_);
v___x_549_ = lean_apply_1(v___x_167__overap_548_, v_toOne_547_);
lean_inc(v___x_549_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_549_);
lean_ctor_set(v___x_539_, 0, v___x_549_);
v___x_551_ = v___x_539_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_566_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_345__overap_553_; lean_object* v___x_554_; lean_object* v_val_555_; lean_object* v_inv_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
lean_inc_ref(v___x_527_);
v___x_552_ = lean_alloc_closure((void*)(lp_mathlib_Function_update___boxed), 7, 6);
lean_closure_set(v___x_552_, 0, lean_box(0));
lean_closure_set(v___x_552_, 1, lean_box(0));
lean_closure_set(v___x_552_, 2, v___x_527_);
lean_closure_set(v___x_552_, 3, v___f_530_);
lean_closure_set(v___x_552_, 4, v_fst_518_);
lean_closure_set(v___x_552_, 5, v___x_551_);
v___x_345__overap_553_ = lp_GRH_New_diagGL___redArg(v___x_527_, v_inst_512_);
v___x_554_ = lean_apply_1(v___x_345__overap_553_, v___x_552_);
v_val_555_ = lean_ctor_get(v___x_554_, 0);
v_inv_556_ = lean_ctor_get(v___x_554_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_565_ == 0)
{
v___x_558_ = v___x_554_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_inv_556_);
lean_inc(v_val_555_);
lean_dec(v___x_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___f_560_; lean_object* v___f_561_; lean_object* v___x_563_; 
lean_inc_ref(v_toAddCommMonoid_542_);
lean_inc(v_toMul_544_);
lean_inc(v___x_526_);
v___f_560_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__5), 8, 6);
lean_closure_set(v___f_560_, 0, v_inv_534_);
lean_closure_set(v___f_560_, 1, v_inv_537_);
lean_closure_set(v___f_560_, 2, v___x_526_);
lean_closure_set(v___f_560_, 3, v_toMul_544_);
lean_closure_set(v___f_560_, 4, v_toAddCommMonoid_542_);
lean_closure_set(v___f_560_, 5, v_inv_556_);
v___f_561_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg___lam__10), 8, 6);
lean_closure_set(v___f_561_, 0, v_val_555_);
lean_closure_set(v___f_561_, 1, v_val_533_);
lean_closure_set(v___f_561_, 2, v_val_536_);
lean_closure_set(v___f_561_, 3, v___x_526_);
lean_closure_set(v___f_561_, 4, v_toMul_544_);
lean_closure_set(v___f_561_, 5, v_toAddCommMonoid_542_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___f_560_);
lean_ctor_set(v___x_558_, 0, v___f_561_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___f_561_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___f_560_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection(lean_object* v_R_570_, lean_object* v_N_571_, lean_object* v_k_572_, lean_object* v_W_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_T_577_, lean_object* v_D_578_, lean_object* v_r_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___redArg(v_k_572_, v_inst_575_, v_T_577_, v_D_578_, v_r_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection___boxed(lean_object* v_R_581_, lean_object* v_N_582_, lean_object* v_k_583_, lean_object* v_W_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_T_588_, lean_object* v_D_589_, lean_object* v_r_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = lp_GRH_New_FrobeniusCycle_RootAt_swapTransvection(v_R_581_, v_N_582_, v_k_583_, v_W_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_T_588_, v_D_589_, v_r_590_);
lean_dec_ref(v_inst_585_);
lean_dec(v_N_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign___redArg(lean_object* v_D_592_, lean_object* v_z_593_){
_start:
{
lean_object* v_fst_594_; lean_object* v_fst_595_; uint8_t v___x_596_; 
v_fst_594_ = lean_ctor_get(v_z_593_, 0);
v_fst_595_ = lean_ctor_get(v_D_592_, 1);
v___x_596_ = lean_nat_dec_eq(v_fst_594_, v_fst_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0, &lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0_once, _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__0);
return v___x_597_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1, &lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1_once, _init_lp_GRH_New_FrobeniusCycle_RootAt_sign___redArg___closed__1);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign___redArg___boxed(lean_object* v_D_599_, lean_object* v_z_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = lp_GRH_New_FrobeniusCycle_RootAt_moveSign___redArg(v_D_599_, v_z_600_);
lean_dec_ref(v_z_600_);
lean_dec_ref(v_D_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign(lean_object* v_R_602_, lean_object* v_N_603_, lean_object* v_k_604_, lean_object* v_W_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_T_609_, lean_object* v_D_610_, lean_object* v_z_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lp_GRH_New_FrobeniusCycle_RootAt_moveSign___redArg(v_D_610_, v_z_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_RootAt_moveSign___boxed(lean_object* v_R_613_, lean_object* v_N_614_, lean_object* v_k_615_, lean_object* v_W_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_T_620_, lean_object* v_D_621_, lean_object* v_z_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = lp_GRH_New_FrobeniusCycle_RootAt_moveSign(v_R_613_, v_N_614_, v_k_615_, v_W_616_, v_inst_617_, v_inst_618_, v_inst_619_, v_T_620_, v_D_621_, v_z_622_);
lean_dec_ref(v_z_622_);
lean_dec_ref(v_D_621_);
lean_dec_ref(v_T_620_);
lean_dec_ref(v_inst_618_);
lean_dec_ref(v_inst_617_);
lean_dec(v_k_615_);
lean_dec(v_N_614_);
return v_res_623_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_TwistingData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_ElementaryDivisors_TwistingData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
