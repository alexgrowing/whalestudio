// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.StatementU
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementKT public import Formalism.RealPlaceAnalysis.StatementC
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(lean_object*);
lean_object* lp_mathlib_Pi_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_WithLp_linearEquiv___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_tree_Formalism_REAL_ew___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_WithLp_instAddCommGroup___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_WithLp_equiv(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_cons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_WithLp_instSMul___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_REAL_isoPart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_pfil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_pfil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coinv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coinv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_REAL_arrOf___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrTo___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_positionsE___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_positionsE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_positionsE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_symSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_symSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrV0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrV0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vplus___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vplus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vplus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vminus___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vminus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vminus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Nset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Nset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_pfil(lean_object* v_V_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_n_4_, lean_object* v_00_u03b5_5_, lean_object* v_E_6_, lean_object* v_u_7_, lean_object* v_j_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_pfil___boxed(lean_object* v_V_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_n_13_, lean_object* v_00_u03b5_14_, lean_object* v_E_15_, lean_object* v_u_16_, lean_object* v_j_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_REAL_pfil(v_V_10_, v_inst_11_, v_inst_12_, v_n_13_, v_00_u03b5_14_, v_E_15_, v_u_16_, v_j_17_);
lean_dec(v_j_17_);
lean_dec(v_u_16_);
lean_dec(v_E_15_);
lean_dec_ref(v_00_u03b5_14_);
lean_dec(v_n_13_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coinv(lean_object* v_V_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_n_22_, lean_object* v_00_u03b5_23_, lean_object* v_E_24_, lean_object* v_00_u039b_25_, lean_object* v_U_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coinv___boxed(lean_object* v_V_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_n_31_, lean_object* v_00_u03b5_32_, lean_object* v_E_33_, lean_object* v_00_u039b_34_, lean_object* v_U_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_REAL_coinv(v_V_28_, v_inst_29_, v_inst_30_, v_n_31_, v_00_u03b5_32_, v_E_33_, v_00_u039b_34_, v_U_35_);
lean_dec(v_00_u039b_34_);
lean_dec(v_E_33_);
lean_dec_ref(v_00_u03b5_32_);
lean_dec(v_n_31_);
lean_dec(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___redArg___lam__0(lean_object* v_inst_37_, lean_object* v_i_38_){
_start:
{
lean_inc_ref(v_inst_37_);
return v_inst_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed(lean_object* v_inst_39_, lean_object* v_i_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_REAL_arrOf___redArg___lam__0(v_inst_39_, v_i_40_);
lean_dec_ref(v_i_40_);
lean_dec_ref(v_inst_39_);
return v_res_41_;
}
}
static lean_object* _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___redArg(lean_object* v_inst_44_){
_start:
{
lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_toLinearMap_49_; 
v___f_45_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_45_, 0, v_inst_44_);
v___x_46_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_47_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_45_);
v___x_48_ = lp_mathlib_WithLp_linearEquiv___redArg(v___x_46_, v___x_47_);
lean_dec_ref(v___x_47_);
v_toLinearMap_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_toLinearMap_49_);
lean_dec_ref(v___x_48_);
return v_toLinearMap_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf(lean_object* v_V_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_j_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_Formalism_REAL_arrOf___redArg(v_inst_51_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrOf___boxed(lean_object* v_V_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_n_59_, lean_object* v_j_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_REAL_arrOf(v_V_56_, v_inst_57_, v_inst_58_, v_n_59_, v_j_60_);
lean_dec(v_j_60_);
lean_dec(v_n_59_);
lean_dec(v_inst_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrTo___redArg(lean_object* v_inst_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_toLinearMap_68_; 
v___f_63_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_63_, 0, v_inst_62_);
v___x_64_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_65_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_63_);
v___x_66_ = lp_mathlib_WithLp_linearEquiv___redArg(v___x_64_, v___x_65_);
lean_dec_ref(v___x_65_);
v___x_67_ = lp_mathlib_LinearEquiv_symm___redArg(v___x_66_);
v_toLinearMap_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_toLinearMap_68_);
lean_dec_ref(v___x_67_);
return v_toLinearMap_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrTo(lean_object* v_V_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_n_72_, lean_object* v_j_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_REAL_arrTo___redArg(v_inst_70_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrTo___boxed(lean_object* v_V_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_n_78_, lean_object* v_j_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_tree_Formalism_REAL_arrTo(v_V_75_, v_inst_76_, v_inst_77_, v_n_78_, v_j_79_);
lean_dec(v_j_79_);
lean_dec(v_n_78_);
lean_dec(v_inst_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__0(lean_object* v_toZero_81_, lean_object* v_x_82_){
_start:
{
lean_inc(v_toZero_81_);
return v_toZero_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__0___boxed(lean_object* v_toZero_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_tree_Formalism_REAL_factorAction___redArg___lam__0(v_toZero_83_, v_x_84_);
lean_dec(v_x_84_);
lean_dec(v_toZero_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__2(lean_object* v_i_86_, lean_object* v_toSub_87_, lean_object* v_d_88_, lean_object* v_toAddMonoid_89_, lean_object* v_j_90_, lean_object* v_c_91_, lean_object* v_00_u03b1_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___x_100_; lean_object* v_fst_101_; lean_object* v_snd_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_126_; 
lean_inc_ref(v_00_u03b1_92_);
lean_inc(v_i_86_);
v___x_100_ = lean_apply_1(v_00_u03b1_92_, v_i_86_);
v_fst_101_ = lean_ctor_get(v___x_100_, 0);
v_snd_102_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_126_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snd_102_);
lean_inc(v_fst_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
v___jp_94_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_inc(v___y_93_);
v___x_97_ = lean_apply_1(v___y_95_, v___y_93_);
v___x_98_ = lean_apply_1(v___y_96_, v___y_93_);
v___x_99_ = lean_apply_2(v_toSub_87_, v___x_97_, v___x_98_);
return v___x_99_;
}
v_resetjp_103_:
{
lean_object* v___y_107_; uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_eq(v_fst_101_, v_c_91_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v_toZero_120_; lean_object* v___f_121_; 
v___x_119_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_89_);
v_toZero_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_toZero_120_);
lean_dec_ref(v___x_119_);
v___f_121_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_factorAction___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_121_, 0, v_toZero_120_);
v___y_107_ = v___f_121_;
goto v___jp_106_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
lean_inc(v_j_90_);
v___x_122_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_122_, 0, v_j_90_);
lean_inc(v_snd_102_);
lean_inc(v_d_88_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_d_88_);
lean_ctor_set(v___x_123_, 1, v_snd_102_);
lean_inc(v_i_86_);
lean_inc_ref(v_00_u03b1_92_);
v___x_124_ = lean_alloc_closure((void*)(lp_mathlib_Function_update___boxed), 7, 6);
lean_closure_set(v___x_124_, 0, lean_box(0));
lean_closure_set(v___x_124_, 1, lean_box(0));
lean_closure_set(v___x_124_, 2, v___x_122_);
lean_closure_set(v___x_124_, 3, v_00_u03b1_92_);
lean_closure_set(v___x_124_, 4, v_i_86_);
lean_closure_set(v___x_124_, 5, v___x_123_);
v___x_125_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_125_, 0, lean_box(0));
lean_closure_set(v___x_125_, 1, lean_box(0));
lean_closure_set(v___x_125_, 2, v___x_124_);
v___y_107_ = v___x_125_;
goto v___jp_106_;
}
v___jp_106_:
{
uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_eq(v_snd_102_, v_d_88_);
lean_dec(v_d_88_);
lean_dec(v_snd_102_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v_toZero_110_; lean_object* v___f_111_; 
lean_del_object(v___x_104_);
lean_dec(v_fst_101_);
lean_dec_ref(v_00_u03b1_92_);
lean_dec(v_c_91_);
lean_dec(v_j_90_);
lean_dec(v_i_86_);
v___x_109_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_89_);
v_toZero_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_toZero_110_);
lean_dec_ref(v___x_109_);
v___f_111_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_factorAction___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_111_, 0, v_toZero_110_);
v___y_95_ = v___y_107_;
v___y_96_ = v___f_111_;
goto v___jp_94_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_112_, 0, v_j_90_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_c_91_);
v___x_114_ = v___x_104_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_fst_101_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_c_91_);
v___x_114_ = v_reuseFailAlloc_117_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_alloc_closure((void*)(lp_mathlib_Function_update___boxed), 7, 6);
lean_closure_set(v___x_115_, 0, lean_box(0));
lean_closure_set(v___x_115_, 1, lean_box(0));
lean_closure_set(v___x_115_, 2, v___x_112_);
lean_closure_set(v___x_115_, 3, v_00_u03b1_92_);
lean_closure_set(v___x_115_, 4, v_i_86_);
lean_closure_set(v___x_115_, 5, v___x_114_);
v___x_116_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, lean_box(0));
lean_closure_set(v___x_116_, 2, v___x_115_);
v___y_95_ = v___y_107_;
v___y_96_ = v___x_116_;
goto v___jp_94_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg___lam__2___boxed(lean_object* v_i_127_, lean_object* v_toSub_128_, lean_object* v_d_129_, lean_object* v_toAddMonoid_130_, lean_object* v_j_131_, lean_object* v_c_132_, lean_object* v_00_u03b1_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_tree_Formalism_REAL_factorAction___redArg___lam__2(v_i_127_, v_toSub_128_, v_d_129_, v_toAddMonoid_130_, v_j_131_, v_c_132_, v_00_u03b1_133_, v___y_134_);
lean_dec_ref(v_toAddMonoid_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___redArg(lean_object* v_inst_136_, lean_object* v_j_137_, lean_object* v_i_138_, lean_object* v_c_139_, lean_object* v_d_140_){
_start:
{
lean_object* v_toAddMonoid_141_; lean_object* v_toSub_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; 
v_toAddMonoid_141_ = lean_ctor_get(v_inst_136_, 0);
v_toSub_142_ = lean_ctor_get(v_inst_136_, 2);
lean_inc_ref(v_toAddMonoid_141_);
lean_inc(v_toSub_142_);
v___f_143_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_factorAction___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_143_, 0, v_i_138_);
lean_closure_set(v___f_143_, 1, v_toSub_142_);
lean_closure_set(v___f_143_, 2, v_d_140_);
lean_closure_set(v___f_143_, 3, v_toAddMonoid_141_);
lean_closure_set(v___f_143_, 4, v_j_137_);
lean_closure_set(v___f_143_, 5, v_c_139_);
lean_inc_ref(v_inst_136_);
v___x_144_ = lp_tree_Formalism_REAL_arrTo___redArg(v_inst_136_);
v___f_145_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_145_, 0, v___f_143_);
v___x_146_ = lp_tree_Formalism_REAL_arrOf___redArg(v_inst_136_);
v___f_147_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_147_, 0, v___x_146_);
lean_closure_set(v___f_147_, 1, v___f_145_);
v___f_148_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_148_, 0, v___f_147_);
lean_closure_set(v___f_148_, 1, v___x_144_);
return v___f_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction(lean_object* v_V_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_n_152_, lean_object* v_j_153_, lean_object* v_i_154_, lean_object* v_c_155_, lean_object* v_d_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lp_tree_Formalism_REAL_factorAction___redArg(v_inst_150_, v_j_153_, v_i_154_, v_c_155_, v_d_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_factorAction___boxed(lean_object* v_V_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_n_161_, lean_object* v_j_162_, lean_object* v_i_163_, lean_object* v_c_164_, lean_object* v_d_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_tree_Formalism_REAL_factorAction(v_V_158_, v_inst_159_, v_inst_160_, v_n_161_, v_j_162_, v_i_163_, v_c_164_, v_d_165_);
lean_dec(v_n_161_);
lean_dec(v_inst_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE___redArg___lam__0(lean_object* v_E_167_, lean_object* v_c_168_, lean_object* v_d_169_, lean_object* v_00_u03b1_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_apply_2(v_E_167_, v_c_168_, v_d_169_);
v___x_173_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, lean_box(0));
lean_closure_set(v___x_173_, 2, v_00_u03b1_170_);
v___x_174_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___x_173_, v___x_172_, v___y_171_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE___redArg(lean_object* v_inst_175_, lean_object* v_E_176_, lean_object* v_c_177_, lean_object* v_d_178_){
_start:
{
lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___f_184_; 
v___f_179_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_ptE___redArg___lam__0), 5, 3);
lean_closure_set(v___f_179_, 0, v_E_176_);
lean_closure_set(v___f_179_, 1, v_c_177_);
lean_closure_set(v___f_179_, 2, v_d_178_);
lean_inc_ref(v_inst_175_);
v___x_180_ = lp_tree_Formalism_REAL_arrTo___redArg(v_inst_175_);
v___f_181_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_181_, 0, v___f_179_);
v___x_182_ = lp_tree_Formalism_REAL_arrOf___redArg(v_inst_175_);
v___f_183_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_183_, 0, v___x_182_);
lean_closure_set(v___f_183_, 1, v___f_181_);
v___f_184_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_184_, 0, v___f_183_);
lean_closure_set(v___f_184_, 1, v___x_180_);
return v___f_184_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE(lean_object* v_V_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_n_188_, lean_object* v_j_189_, lean_object* v_E_190_, lean_object* v_c_191_, lean_object* v_d_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lp_tree_Formalism_REAL_ptE___redArg(v_inst_186_, v_E_190_, v_c_191_, v_d_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_ptE___boxed(lean_object* v_V_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_n_197_, lean_object* v_j_198_, lean_object* v_E_199_, lean_object* v_c_200_, lean_object* v_d_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lp_tree_Formalism_REAL_ptE(v_V_194_, v_inst_195_, v_inst_196_, v_n_197_, v_j_198_, v_E_199_, v_c_200_, v_d_201_);
lean_dec(v_j_198_);
lean_dec(v_n_197_);
lean_dec(v_inst_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__1(lean_object* v_inst_203_, lean_object* v_j_204_, lean_object* v_c_205_, lean_object* v_d_206_, lean_object* v_i_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_251__overap_210_; lean_object* v___x_211_; 
v___x_251__overap_210_ = lp_tree_Formalism_REAL_factorAction___redArg(v_inst_203_, v_j_204_, v_i_207_, v_c_205_, v_d_206_);
v___x_211_ = lean_apply_2(v___x_251__overap_210_, v___y_208_, v___y_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__0(lean_object* v_toAddMonoid_212_, lean_object* v_toFun_213_, lean_object* v___x_214_, lean_object* v___x_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_toAddSemigroup_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_toAddSemigroup_217_ = lean_ctor_get(v_toAddMonoid_212_, 0);
lean_inc(v_toAddSemigroup_217_);
lean_dec_ref(v_toAddMonoid_212_);
lean_inc(v_toFun_213_);
lean_inc_ref(v___y_216_);
v___x_218_ = lean_apply_2(v_toFun_213_, v___x_214_, v___y_216_);
v___x_219_ = lean_apply_2(v_toFun_213_, v___x_215_, v___y_216_);
v___x_220_ = lean_apply_2(v_toAddSemigroup_217_, v___x_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__2(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v___f_224_, lean_object* v_inst_225_, lean_object* v_E_226_, lean_object* v_c_227_, lean_object* v_d_228_, lean_object* v_toAddMonoid_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_232_; lean_object* v_toFun_233_; lean_object* v_invFun_234_; lean_object* v___x_266__overap_235_; lean_object* v___x_236_; lean_object* v___x_267__overap_237_; lean_object* v___x_238_; lean_object* v___f_239_; lean_object* v___x_240_; 
v___x_232_ = lp_mathlib_WithLp_equiv(v___x_221_, lean_box(0));
v_toFun_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_toFun_233_);
v_invFun_234_ = lean_ctor_get(v___x_232_, 1);
lean_inc(v_invFun_234_);
lean_dec_ref(v___x_232_);
v___x_266__overap_235_ = lp_mathlib_Finset_sum___redArg(v___x_222_, v___x_223_, v___f_224_);
lean_inc(v___y_230_);
v___x_236_ = lean_apply_1(v___x_266__overap_235_, v___y_230_);
v___x_267__overap_237_ = lp_tree_Formalism_REAL_ptE___redArg(v_inst_225_, v_E_226_, v_c_227_, v_d_228_);
v___x_238_ = lean_apply_1(v___x_267__overap_237_, v___y_230_);
v___f_239_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrE___redArg___lam__0), 5, 4);
lean_closure_set(v___f_239_, 0, v_toAddMonoid_229_);
lean_closure_set(v___f_239_, 1, v_toFun_233_);
lean_closure_set(v___f_239_, 2, v___x_236_);
lean_closure_set(v___f_239_, 3, v___x_238_);
v___x_240_ = lean_apply_2(v_invFun_234_, v___f_239_, v___y_231_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg___lam__2___boxed(lean_object* v___x_241_, lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v___f_244_, lean_object* v_inst_245_, lean_object* v_E_246_, lean_object* v_c_247_, lean_object* v_d_248_, lean_object* v_toAddMonoid_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_tree_Formalism_REAL_arrE___redArg___lam__2(v___x_241_, v___x_242_, v___x_243_, v___f_244_, v_inst_245_, v_E_246_, v_c_247_, v_d_248_, v_toAddMonoid_249_, v___y_250_, v___y_251_);
lean_dec_ref(v___x_242_);
lean_dec(v___x_241_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___redArg(lean_object* v_inst_253_, lean_object* v_E_254_, lean_object* v_j_255_, lean_object* v_c_256_, lean_object* v_d_257_){
_start:
{
lean_object* v_toAddMonoid_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_toAddMonoid_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___f_267_; 
v_toAddMonoid_258_ = lean_ctor_get(v_inst_253_, 0);
lean_inc_ref(v_toAddMonoid_258_);
lean_inc_ref_n(v_inst_253_, 2);
v___f_259_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_259_, 0, v_inst_253_);
v___x_260_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_261_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_259_);
v___x_262_ = lp_mathlib_WithLp_instAddCommGroup___redArg(v___x_260_, v___x_261_);
v_toAddMonoid_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc_ref(v_toAddMonoid_263_);
lean_dec_ref(v___x_262_);
lean_inc(v_d_257_);
lean_inc(v_c_256_);
lean_inc(v_j_255_);
v___f_264_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrE___redArg___lam__1), 7, 4);
lean_closure_set(v___f_264_, 0, v_inst_253_);
lean_closure_set(v___f_264_, 1, v_j_255_);
lean_closure_set(v___f_264_, 2, v_c_256_);
lean_closure_set(v___f_264_, 3, v_d_257_);
v___x_265_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_263_);
v___x_266_ = l_List_finRange(v_j_255_);
v___f_267_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrE___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_267_, 0, v___x_260_);
lean_closure_set(v___f_267_, 1, v___x_265_);
lean_closure_set(v___f_267_, 2, v___x_266_);
lean_closure_set(v___f_267_, 3, v___f_264_);
lean_closure_set(v___f_267_, 4, v_inst_253_);
lean_closure_set(v___f_267_, 5, v_E_254_);
lean_closure_set(v___f_267_, 6, v_c_256_);
lean_closure_set(v___f_267_, 7, v_d_257_);
lean_closure_set(v___f_267_, 8, v_toAddMonoid_258_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE(lean_object* v_V_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_n_271_, lean_object* v_E_272_, lean_object* v_j_273_, lean_object* v_c_274_, lean_object* v_d_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lp_tree_Formalism_REAL_arrE___redArg(v_inst_269_, v_E_272_, v_j_273_, v_c_274_, v_d_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrE___boxed(lean_object* v_V_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_n_280_, lean_object* v_E_281_, lean_object* v_j_282_, lean_object* v_c_283_, lean_object* v_d_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = lp_tree_Formalism_REAL_arrE(v_V_277_, v_inst_278_, v_inst_279_, v_n_280_, v_E_281_, v_j_282_, v_c_283_, v_d_284_);
lean_dec(v_n_280_);
lean_dec(v_inst_279_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_positionsE___redArg(lean_object* v_inst_286_, lean_object* v_j_287_, lean_object* v_c_288_, lean_object* v_d_289_){
_start:
{
lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_toAddMonoid_294_; lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_inc_ref(v_inst_286_);
v___f_290_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_290_, 0, v_inst_286_);
v___x_291_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_292_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_290_);
v___x_293_ = lp_mathlib_WithLp_instAddCommGroup___redArg(v___x_291_, v___x_292_);
v_toAddMonoid_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_toAddMonoid_294_);
lean_dec_ref(v___x_293_);
lean_inc(v_j_287_);
v___f_295_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrE___redArg___lam__1), 7, 4);
lean_closure_set(v___f_295_, 0, v_inst_286_);
lean_closure_set(v___f_295_, 1, v_j_287_);
lean_closure_set(v___f_295_, 2, v_c_288_);
lean_closure_set(v___f_295_, 3, v_d_289_);
v___x_296_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_294_);
v___x_297_ = l_List_finRange(v_j_287_);
v___x_298_ = lp_mathlib_Finset_sum___redArg(v___x_296_, v___x_297_, v___f_295_);
lean_dec_ref(v___x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_positionsE(lean_object* v_V_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_n_302_, lean_object* v_j_303_, lean_object* v_c_304_, lean_object* v_d_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lp_tree_Formalism_REAL_positionsE___redArg(v_inst_300_, v_j_303_, v_c_304_, v_d_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_positionsE___boxed(lean_object* v_V_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_n_310_, lean_object* v_j_311_, lean_object* v_c_312_, lean_object* v_d_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = lp_tree_Formalism_REAL_positionsE(v_V_307_, v_inst_308_, v_inst_309_, v_n_310_, v_j_311_, v_c_312_, v_d_313_);
lean_dec(v_n_310_);
lean_dec(v_inst_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__1(lean_object* v_inst_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_toAddMonoid_317_; lean_object* v___x_318_; lean_object* v_toZero_319_; 
v_toAddMonoid_317_ = lean_ctor_get(v_inst_315_, 0);
v___x_318_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_317_);
v_toZero_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_toZero_319_);
lean_dec_ref(v___x_318_);
return v_toZero_319_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__1___boxed(lean_object* v_inst_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = lp_tree_Formalism_REAL_OmS___redArg___lam__1(v_inst_320_, v_x_321_);
lean_dec_ref(v_x_321_);
lean_dec_ref(v_inst_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__0(lean_object* v___x_323_, lean_object* v___f_324_, lean_object* v_inst_325_, lean_object* v_j_326_, lean_object* v_i_327_, lean_object* v_c_328_, lean_object* v_E_329_, lean_object* v_00_u03b5_330_, lean_object* v_d_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
lean_inc_ref(v_00_u03b5_330_);
lean_inc(v_c_328_);
v___x_343_ = lean_apply_1(v_00_u03b5_330_, v_c_328_);
lean_inc(v_d_331_);
v___x_344_ = lean_apply_1(v_00_u03b5_330_, v_d_331_);
v___x_345_ = lean_unbox(v___x_343_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = lean_unbox(v___x_344_);
if (v___x_346_ == 0)
{
lean_dec(v___f_324_);
goto v___jp_338_;
}
else
{
lean_dec(v___y_332_);
lean_dec(v_d_331_);
lean_dec(v_E_329_);
lean_dec(v_c_328_);
lean_dec(v_i_327_);
lean_dec(v_j_326_);
lean_dec_ref(v_inst_325_);
goto v___jp_334_;
}
}
else
{
uint8_t v___x_347_; 
v___x_347_ = lean_unbox(v___x_344_);
if (v___x_347_ == 0)
{
lean_dec(v___y_332_);
lean_dec(v_d_331_);
lean_dec(v_E_329_);
lean_dec(v_c_328_);
lean_dec(v_i_327_);
lean_dec(v_j_326_);
lean_dec_ref(v_inst_325_);
goto v___jp_334_;
}
else
{
lean_dec(v___f_324_);
goto v___jp_338_;
}
}
v___jp_334_:
{
lean_object* v___x_335_; lean_object* v_invFun_336_; lean_object* v___x_337_; 
v___x_335_ = lp_mathlib_WithLp_equiv(v___x_323_, lean_box(0));
v_invFun_336_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_invFun_336_);
lean_dec_ref(v___x_335_);
v___x_337_ = lean_apply_2(v_invFun_336_, v___f_324_, v___y_333_);
return v___x_337_;
}
v___jp_338_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_318__overap_341_; lean_object* v___x_342_; 
lean_inc(v_d_331_);
lean_inc(v_c_328_);
lean_inc_ref(v_inst_325_);
v___x_339_ = lp_tree_Formalism_REAL_factorAction___redArg(v_inst_325_, v_j_326_, v_i_327_, v_c_328_, v_d_331_);
v___x_340_ = lp_tree_Formalism_REAL_ptE___redArg(v_inst_325_, v_E_329_, v_d_331_, v_c_328_);
v___x_318__overap_341_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___x_340_, v___x_339_, v___y_332_);
v___x_342_ = lean_apply_1(v___x_318__overap_341_, v___y_333_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__0___boxed(lean_object* v___x_348_, lean_object* v___f_349_, lean_object* v_inst_350_, lean_object* v_j_351_, lean_object* v_i_352_, lean_object* v_c_353_, lean_object* v_E_354_, lean_object* v_00_u03b5_355_, lean_object* v_d_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = lp_tree_Formalism_REAL_OmS___redArg___lam__0(v___x_348_, v___f_349_, v_inst_350_, v_j_351_, v_i_352_, v_c_353_, v_E_354_, v_00_u03b5_355_, v_d_356_, v___y_357_, v___y_358_);
lean_dec(v___x_348_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__2(lean_object* v___x_360_, lean_object* v___f_361_, lean_object* v_inst_362_, lean_object* v_j_363_, lean_object* v_i_364_, lean_object* v_E_365_, lean_object* v_00_u03b5_366_, lean_object* v___x_367_, lean_object* v___x_368_, lean_object* v_c_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___x_329__overap_373_; lean_object* v___x_374_; 
v___f_372_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_OmS___redArg___lam__0___boxed), 11, 8);
lean_closure_set(v___f_372_, 0, v___x_360_);
lean_closure_set(v___f_372_, 1, v___f_361_);
lean_closure_set(v___f_372_, 2, v_inst_362_);
lean_closure_set(v___f_372_, 3, v_j_363_);
lean_closure_set(v___f_372_, 4, v_i_364_);
lean_closure_set(v___f_372_, 5, v_c_369_);
lean_closure_set(v___f_372_, 6, v_E_365_);
lean_closure_set(v___f_372_, 7, v_00_u03b5_366_);
v___x_329__overap_373_ = lp_mathlib_Finset_sum___redArg(v___x_367_, v___x_368_, v___f_372_);
v___x_374_ = lean_apply_2(v___x_329__overap_373_, v___y_370_, v___y_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg___lam__2___boxed(lean_object* v___x_375_, lean_object* v___f_376_, lean_object* v_inst_377_, lean_object* v_j_378_, lean_object* v_i_379_, lean_object* v_E_380_, lean_object* v_00_u03b5_381_, lean_object* v___x_382_, lean_object* v___x_383_, lean_object* v_c_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = lp_tree_Formalism_REAL_OmS___redArg___lam__2(v___x_375_, v___f_376_, v_inst_377_, v_j_378_, v_i_379_, v_E_380_, v_00_u03b5_381_, v___x_382_, v___x_383_, v_c_384_, v___y_385_, v___y_386_);
lean_dec_ref(v___x_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___redArg(lean_object* v_inst_388_, lean_object* v_n_389_, lean_object* v_j_390_, lean_object* v_00_u03b5_391_, lean_object* v_E_392_, lean_object* v_i_393_){
_start:
{
lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_toAddMonoid_398_; lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___f_402_; lean_object* v___x_403_; 
lean_inc_ref_n(v_inst_388_, 2);
v___f_394_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_394_, 0, v_inst_388_);
v___x_395_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_396_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_394_);
v___x_397_ = lp_mathlib_WithLp_instAddCommGroup___redArg(v___x_395_, v___x_396_);
v_toAddMonoid_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_toAddMonoid_398_);
lean_dec_ref(v___x_397_);
v___f_399_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_OmS___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_399_, 0, v_inst_388_);
v___x_400_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_398_);
v___x_401_ = l_List_finRange(v_n_389_);
lean_inc(v___x_401_);
lean_inc_ref(v___x_400_);
v___f_402_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_OmS___redArg___lam__2___boxed), 12, 9);
lean_closure_set(v___f_402_, 0, v___x_395_);
lean_closure_set(v___f_402_, 1, v___f_399_);
lean_closure_set(v___f_402_, 2, v_inst_388_);
lean_closure_set(v___f_402_, 3, v_j_390_);
lean_closure_set(v___f_402_, 4, v_i_393_);
lean_closure_set(v___f_402_, 5, v_E_392_);
lean_closure_set(v___f_402_, 6, v_00_u03b5_391_);
lean_closure_set(v___f_402_, 7, v___x_400_);
lean_closure_set(v___f_402_, 8, v___x_401_);
v___x_403_ = lp_mathlib_Finset_sum___redArg(v___x_400_, v___x_401_, v___f_402_);
lean_dec_ref(v___x_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS(lean_object* v_V_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_n_407_, lean_object* v_j_408_, lean_object* v_00_u03b5_409_, lean_object* v_E_410_, lean_object* v_i_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lp_tree_Formalism_REAL_OmS___redArg(v_inst_405_, v_n_407_, v_j_408_, v_00_u03b5_409_, v_E_410_, v_i_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_OmS___boxed(lean_object* v_V_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_n_416_, lean_object* v_j_417_, lean_object* v_00_u03b5_418_, lean_object* v_E_419_, lean_object* v_i_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = lp_tree_Formalism_REAL_OmS(v_V_413_, v_inst_414_, v_inst_415_, v_n_416_, v_j_417_, v_00_u03b5_418_, v_E_419_, v_i_420_);
lean_dec(v_inst_415_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg___lam__0(lean_object* v_n_422_, lean_object* v_x_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = l_List_finRange(v_n_422_);
lean_inc(v___x_424_);
v___x_425_ = lp_mathlib_Multiset_product___redArg(v___x_424_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg___lam__0___boxed(lean_object* v_n_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = lp_tree_Formalism_REAL_thetaA___redArg___lam__0(v_n_426_, v_x_427_);
lean_dec(v_x_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg___lam__1(lean_object* v_j_429_, lean_object* v_E_430_, lean_object* v_inst_431_, lean_object* v_00_u03b1_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___f_439_; lean_object* v___x_440_; 
lean_inc_ref(v_00_u03b1_432_);
v___x_434_ = l_List_ofFn___redArg(v_j_429_, v_00_u03b1_432_);
v___x_435_ = l_List_reverse___redArg(v___x_434_);
v___x_436_ = lp_tree_Formalism_REAL_ew___redArg(v_E_430_, v___x_435_);
v___x_437_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_437_, 0, lean_box(0));
lean_closure_set(v___x_437_, 1, lean_box(0));
lean_closure_set(v___x_437_, 2, v_00_u03b1_432_);
v___x_438_ = lp_tree_Formalism_REAL_arrOf___redArg(v_inst_431_);
v___f_439_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_439_, 0, v___x_438_);
lean_closure_set(v___f_439_, 1, v___x_437_);
v___x_440_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___f_439_, v___x_436_, v___y_433_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___redArg(lean_object* v_inst_441_, lean_object* v_n_442_, lean_object* v_E_443_, lean_object* v_j_444_){
_start:
{
lean_object* v_toAddMonoid_445_; lean_object* v___f_446_; lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_toAddMonoid_445_ = lean_ctor_get(v_inst_441_, 0);
lean_inc_ref(v_toAddMonoid_445_);
v___f_446_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_thetaA___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_446_, 0, v_n_442_);
lean_inc_n(v_j_444_, 2);
v___f_447_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_thetaA___redArg___lam__1), 5, 3);
lean_closure_set(v___f_447_, 0, v_j_444_);
lean_closure_set(v___f_447_, 1, v_E_443_);
lean_closure_set(v___f_447_, 2, v_inst_441_);
v___x_448_ = l_List_finRange(v_j_444_);
v___x_449_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_445_);
v___x_450_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_450_, 0, v_j_444_);
v___x_451_ = lp_mathlib_Fintype_piFinset___redArg(v___x_450_, v___x_448_, v___f_446_);
v___x_452_ = lp_mathlib_Finset_sum___redArg(v___x_449_, v___x_451_, v___f_447_);
lean_dec_ref(v___x_449_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA(lean_object* v_V_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_n_456_, lean_object* v_E_457_, lean_object* v_j_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lp_tree_Formalism_REAL_thetaA___redArg(v_inst_454_, v_n_456_, v_E_457_, v_j_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_thetaA___boxed(lean_object* v_V_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_n_463_, lean_object* v_E_464_, lean_object* v_j_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = lp_tree_Formalism_REAL_thetaA(v_V_460_, v_inst_461_, v_inst_462_, v_n_463_, v_E_464_, v_j_465_);
lean_dec(v_inst_462_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___redArg___lam__0(lean_object* v_00_u03c3_467_, lean_object* v_00_u03b1_468_, lean_object* v_i_469_){
_start:
{
lean_object* v_toFun_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_toFun_470_ = lean_ctor_get(v_00_u03c3_467_, 0);
lean_inc(v_toFun_470_);
lean_dec_ref(v_00_u03c3_467_);
v___x_471_ = lean_apply_1(v_toFun_470_, v_i_469_);
v___x_472_ = lean_apply_1(v_00_u03b1_468_, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___redArg___lam__1(lean_object* v_00_u03c3_473_, lean_object* v_00_u03b1_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___f_476_; lean_object* v___x_477_; 
v___f_476_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_permArr___redArg___lam__0), 3, 2);
lean_closure_set(v___f_476_, 0, v_00_u03c3_473_);
lean_closure_set(v___f_476_, 1, v_00_u03b1_474_);
v___x_477_ = lean_apply_1(v___y_475_, v___f_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___redArg(lean_object* v_inst_478_, lean_object* v_00_u03c3_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___f_485_; 
v___f_480_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_permArr___redArg___lam__1), 3, 1);
lean_closure_set(v___f_480_, 0, v_00_u03c3_479_);
lean_inc_ref(v_inst_478_);
v___x_481_ = lp_tree_Formalism_REAL_arrTo___redArg(v_inst_478_);
v___f_482_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_482_, 0, v___f_480_);
v___x_483_ = lp_tree_Formalism_REAL_arrOf___redArg(v_inst_478_);
v___f_484_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_484_, 0, v___x_483_);
lean_closure_set(v___f_484_, 1, v___f_482_);
v___f_485_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_485_, 0, v___f_484_);
lean_closure_set(v___f_485_, 1, v___x_481_);
return v___f_485_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr(lean_object* v_V_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_n_489_, lean_object* v_j_490_, lean_object* v_00_u03c3_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lp_tree_Formalism_REAL_permArr___redArg(v_inst_487_, v_00_u03c3_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_permArr___boxed(lean_object* v_V_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_n_496_, lean_object* v_j_497_, lean_object* v_00_u03c3_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = lp_tree_Formalism_REAL_permArr(v_V_493_, v_inst_494_, v_inst_495_, v_n_496_, v_j_497_, v_00_u03c3_498_);
lean_dec(v_j_497_);
lean_dec(v_n_496_);
lean_dec(v_inst_495_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_symSub(lean_object* v_V_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_n_503_, lean_object* v_j_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_box(0);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_symSub___boxed(lean_object* v_V_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_n_509_, lean_object* v_j_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = lp_tree_Formalism_REAL_symSub(v_V_506_, v_inst_507_, v_inst_508_, v_n_509_, v_j_510_);
lean_dec(v_j_510_);
lean_dec(v_n_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrV0(lean_object* v_V_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_n_515_, lean_object* v_00_u03b5_516_, lean_object* v_E_517_, lean_object* v_u_518_, lean_object* v_j_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_arrV0___boxed(lean_object* v_V_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_n_524_, lean_object* v_00_u03b5_525_, lean_object* v_E_526_, lean_object* v_u_527_, lean_object* v_j_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = lp_tree_Formalism_REAL_arrV0(v_V_521_, v_inst_522_, v_inst_523_, v_n_524_, v_00_u03b5_525_, v_E_526_, v_u_527_, v_j_528_);
lean_dec(v_j_528_);
lean_dec(v_u_527_);
lean_dec(v_E_526_);
lean_dec_ref(v_00_u03b5_525_);
lean_dec(v_n_524_);
lean_dec(v_inst_523_);
lean_dec_ref(v_inst_522_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___redArg___lam__0(lean_object* v___x_530_, lean_object* v_j_531_, lean_object* v_00_u03b1_x27_532_, lean_object* v_00_u03b2_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_nat_mod(v___x_535_, v___x_530_);
v___x_537_ = lean_apply_1(v_00_u03b2_533_, v___x_536_);
v___x_538_ = lean_alloc_closure((void*)(lp_mathlib_Fin_cons___boxed), 5, 4);
lean_closure_set(v___x_538_, 0, v_j_531_);
lean_closure_set(v___x_538_, 1, lean_box(0));
lean_closure_set(v___x_538_, 2, v___x_537_);
lean_closure_set(v___x_538_, 3, v_00_u03b1_x27_532_);
v___x_539_ = lean_apply_1(v___y_534_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___redArg___lam__0___boxed(lean_object* v___x_540_, lean_object* v_j_541_, lean_object* v_00_u03b1_x27_542_, lean_object* v_00_u03b2_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = lp_tree_Formalism_REAL_sliceLin___redArg___lam__0(v___x_540_, v_j_541_, v_00_u03b1_x27_542_, v_00_u03b2_543_, v___y_544_);
lean_dec(v___x_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___redArg(lean_object* v_inst_546_, lean_object* v_j_547_, lean_object* v_00_u03b1_x27_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___f_555_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___f_550_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_sliceLin___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_550_, 0, v___x_549_);
lean_closure_set(v___f_550_, 1, v_j_547_);
lean_closure_set(v___f_550_, 2, v_00_u03b1_x27_548_);
lean_inc_ref(v_inst_546_);
v___x_551_ = lp_tree_Formalism_REAL_arrTo___redArg(v_inst_546_);
v___f_552_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_552_, 0, v___f_550_);
v___x_553_ = lp_tree_Formalism_REAL_arrOf___redArg(v_inst_546_);
v___f_554_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_554_, 0, v___x_553_);
lean_closure_set(v___f_554_, 1, v___f_552_);
v___f_555_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_555_, 0, v___f_554_);
lean_closure_set(v___f_555_, 1, v___x_551_);
return v___f_555_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin(lean_object* v_V_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_n_559_, lean_object* v_j_560_, lean_object* v_00_u03b1_x27_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lp_tree_Formalism_REAL_sliceLin___redArg(v_inst_557_, v_j_560_, v_00_u03b1_x27_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sliceLin___boxed(lean_object* v_V_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_n_566_, lean_object* v_j_567_, lean_object* v_00_u03b1_x27_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = lp_tree_Formalism_REAL_sliceLin(v_V_563_, v_inst_564_, v_inst_565_, v_n_566_, v_j_567_, v_00_u03b1_x27_568_);
lean_dec(v_n_566_);
lean_dec(v_inst_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vplus___redArg(lean_object* v_inst_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v___f_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___f_572_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_572_, 0, v_inst_570_);
v___x_573_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_574_ = lp_mathlib_Pi_Function_module___redArg(v_inst_571_);
v___x_575_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_572_);
v___x_576_ = lp_mathlib_WithLp_instAddCommGroup___redArg(v___x_573_, v___x_575_);
v___x_577_ = lp_mathlib_WithLp_instSMul___redArg(v___x_573_, v___x_574_);
v___x_578_ = lp_tree_Formalism_REAL_isoPart___redArg(v___x_576_, v___x_577_);
lean_dec(v___x_577_);
lean_dec_ref(v___x_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vplus(lean_object* v_V_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_n_582_, lean_object* v_00_u03b5_583_, lean_object* v_E_584_, lean_object* v_00_u039b_585_, lean_object* v_u_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lp_tree_Formalism_REAL_Vplus___redArg(v_inst_580_, v_inst_581_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vplus___boxed(lean_object* v_V_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_n_591_, lean_object* v_00_u03b5_592_, lean_object* v_E_593_, lean_object* v_00_u039b_594_, lean_object* v_u_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = lp_tree_Formalism_REAL_Vplus(v_V_588_, v_inst_589_, v_inst_590_, v_n_591_, v_00_u03b5_592_, v_E_593_, v_00_u039b_594_, v_u_595_);
lean_dec(v_u_595_);
lean_dec(v_00_u039b_594_);
lean_dec(v_E_593_);
lean_dec_ref(v_00_u03b5_592_);
lean_dec(v_n_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vminus___redArg(lean_object* v_inst_597_, lean_object* v_inst_598_){
_start:
{
lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___f_599_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_arrOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_599_, 0, v_inst_597_);
v___x_600_ = lean_obj_once(&lp_tree_Formalism_REAL_arrOf___redArg___closed__0, &lp_tree_Formalism_REAL_arrOf___redArg___closed__0_once, _init_lp_tree_Formalism_REAL_arrOf___redArg___closed__0);
v___x_601_ = lp_mathlib_Pi_Function_module___redArg(v_inst_598_);
v___x_602_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_599_);
v___x_603_ = lp_mathlib_WithLp_instAddCommGroup___redArg(v___x_600_, v___x_602_);
v___x_604_ = lp_mathlib_WithLp_instSMul___redArg(v___x_600_, v___x_601_);
v___x_605_ = lp_tree_Formalism_REAL_isoPart___redArg(v___x_603_, v___x_604_);
lean_dec(v___x_604_);
lean_dec_ref(v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vminus(lean_object* v_V_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_n_609_, lean_object* v_00_u03b5_610_, lean_object* v_E_611_, lean_object* v_00_u039b_612_, lean_object* v_u_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lp_tree_Formalism_REAL_Vminus___redArg(v_inst_607_, v_inst_608_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Vminus___boxed(lean_object* v_V_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_n_618_, lean_object* v_00_u03b5_619_, lean_object* v_E_620_, lean_object* v_00_u039b_621_, lean_object* v_u_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = lp_tree_Formalism_REAL_Vminus(v_V_615_, v_inst_616_, v_inst_617_, v_n_618_, v_00_u03b5_619_, v_E_620_, v_00_u039b_621_, v_u_622_);
lean_dec(v_u_622_);
lean_dec(v_00_u039b_621_);
lean_dec(v_E_620_);
lean_dec_ref(v_00_u03b5_619_);
lean_dec(v_n_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Nset(lean_object* v_V_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_n_627_, lean_object* v_00_u03b5_628_, lean_object* v_E_629_, lean_object* v_00_u039b_630_, lean_object* v_u_631_, lean_object* v_j_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Nset___boxed(lean_object* v_V_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_n_637_, lean_object* v_00_u03b5_638_, lean_object* v_E_639_, lean_object* v_00_u039b_640_, lean_object* v_u_641_, lean_object* v_j_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = lp_tree_Formalism_REAL_Nset(v_V_634_, v_inst_635_, v_inst_636_, v_n_637_, v_00_u03b5_638_, v_E_639_, v_00_u039b_640_, v_u_641_, v_j_642_);
lean_dec(v_j_642_);
lean_dec(v_u_641_);
lean_dec(v_00_u039b_640_);
lean_dec(v_E_639_);
lean_dec_ref(v_00_u03b5_638_);
lean_dec(v_n_637_);
lean_dec(v_inst_636_);
lean_dec_ref(v_inst_635_);
return v_res_643_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementKT(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementU(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementKT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
