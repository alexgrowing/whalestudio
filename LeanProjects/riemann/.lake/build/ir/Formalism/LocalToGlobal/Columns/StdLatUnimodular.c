// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.StdLatUnimodular
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.StatementLat public import Formalism.HermitianLattices.DualOrthSum public import Formalism.HermitianLattices.NeighbourConstruct public import Formalism.SatakeDualWeyl.StatementB public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Fin_snoc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_ring___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_mulVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_single___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_castSucc___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UF(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UF___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_initL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_initL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_initL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_z0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_z0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_at(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_at___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_kerAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_kerAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_L(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_L___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Lsh(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Lsh___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dnN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dnN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_tilN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_tilN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_dia___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_dia(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_dia___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___lam__0(lean_object* v_x_1_, lean_object* v_inst_2_, lean_object* v_y_3_, lean_object* v_toMul_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc(v_i_5_);
v___x_6_ = lean_apply_1(v_x_1_, v_i_5_);
v___x_7_ = lean_apply_1(v_inst_2_, v___x_6_);
v___x_8_ = lean_apply_1(v_y_3_, v_i_5_);
v___x_9_ = lean_apply_2(v_toMul_4_, v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___lam__1(lean_object* v_inst_10_, lean_object* v_toMul_11_, lean_object* v_n_12_, lean_object* v_toAddCommMonoid_13_, lean_object* v_x_14_, lean_object* v_y_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_hStd___redArg___lam__0), 5, 4);
lean_closure_set(v___f_16_, 0, v_x_14_);
lean_closure_set(v___f_16_, 1, v_inst_10_);
lean_closure_set(v___f_16_, 2, v_y_15_);
lean_closure_set(v___f_16_, 3, v_toMul_11_);
v___x_17_ = l_List_finRange(v_n_12_);
v___x_18_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_13_, v___x_17_, v___f_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___lam__1___boxed(lean_object* v_inst_19_, lean_object* v_toMul_20_, lean_object* v_n_21_, lean_object* v_toAddCommMonoid_22_, lean_object* v_x_23_, lean_object* v_y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_L2_Col_hStd___redArg___lam__1(v_inst_19_, v_toMul_20_, v_n_21_, v_toAddCommMonoid_22_, v_x_23_, v_y_24_);
lean_dec_ref(v_toAddCommMonoid_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg(lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_n_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_toSemiring_31_; lean_object* v_toAddCommMonoid_32_; lean_object* v___x_33_; lean_object* v_toMul_34_; lean_object* v___f_35_; lean_object* v___f_36_; 
v___x_29_ = lp_mathlib_Field_toSemifield___redArg(v_inst_26_);
v___x_30_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_29_);
v_toSemiring_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc_ref(v_toSemiring_31_);
lean_dec_ref(v___x_30_);
v_toAddCommMonoid_32_ = lean_ctor_get(v_toSemiring_31_, 0);
lean_inc_ref(v_toAddCommMonoid_32_);
v___x_33_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_31_);
v_toMul_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_toMul_34_);
lean_dec_ref(v___x_33_);
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_hStd___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_35_, 0, v_inst_27_);
lean_closure_set(v___f_35_, 1, v_toMul_34_);
lean_closure_set(v___f_35_, 2, v_n_28_);
lean_closure_set(v___f_35_, 3, v_toAddCommMonoid_32_);
v___f_36_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0), 3, 1);
lean_closure_set(v___f_36_, 0, v___f_35_);
return v___f_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___redArg___boxed(lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_n_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Col_hStd___redArg(v_inst_37_, v_inst_38_, v_n_39_);
lean_dec_ref(v_inst_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd(lean_object* v_E_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_n_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_tree_Formalism_L2_Col_hStd___redArg(v_inst_42_, v_inst_43_, v_n_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hStd___boxed(lean_object* v_E_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_n_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_L2_Col_hStd(v_E_46_, v_inst_47_, v_inst_48_, v_n_49_);
lean_dec_ref(v_inst_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UF(lean_object* v_E_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_n_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(0);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UF___boxed(lean_object* v_E_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_n_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_L2_Col_UF(v_E_56_, v_inst_57_, v_inst_58_, v_n_59_);
lean_dec(v_n_59_);
lean_dec(v_inst_58_);
lean_dec_ref(v_inst_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg___lam__0(lean_object* v_n_61_, lean_object* v_toZero_62_, lean_object* v_x_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_mathlib_Fin_snoc___redArg(v_n_61_, v_x_63_, v_toZero_62_, v___y_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg___lam__0___boxed(lean_object* v_n_66_, lean_object* v_toZero_67_, lean_object* v_x_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_L2_Col_incl___redArg___lam__0(v_n_66_, v_toZero_67_, v_x_68_, v___y_69_);
lean_dec(v_toZero_67_);
lean_dec(v_n_66_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg(lean_object* v_inst_71_, lean_object* v_n_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_toSemiring_75_; lean_object* v___x_76_; lean_object* v_toZero_77_; lean_object* v___f_78_; 
v___x_73_ = lp_mathlib_Field_toSemifield___redArg(v_inst_71_);
v___x_74_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_73_);
v_toSemiring_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_ref(v_toSemiring_75_);
lean_dec_ref(v___x_74_);
v___x_76_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_75_);
v_toZero_77_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_toZero_77_);
lean_dec_ref(v___x_76_);
v___f_78_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_incl___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_78_, 0, v_n_72_);
lean_closure_set(v___f_78_, 1, v_toZero_77_);
return v___f_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___redArg___boxed(lean_object* v_inst_79_, lean_object* v_n_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_Formalism_L2_Col_incl___redArg(v_inst_79_, v_n_80_);
lean_dec_ref(v_inst_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl(lean_object* v_E_82_, lean_object* v_inst_83_, lean_object* v_n_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_tree_Formalism_L2_Col_incl___redArg(v_inst_83_, v_n_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_incl___boxed(lean_object* v_E_86_, lean_object* v_inst_87_, lean_object* v_n_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_tree_Formalism_L2_Col_incl(v_E_86_, v_inst_87_, v_n_88_);
lean_dec_ref(v_inst_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_initL___redArg(lean_object* v_n_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___f_92_; 
v___x_91_ = lean_alloc_closure((void*)(l_Fin_castSucc___boxed), 2, 1);
lean_closure_set(v___x_91_, 0, v_n_90_);
v___f_92_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_funLeft___redArg___lam__0), 3, 1);
lean_closure_set(v___f_92_, 0, v___x_91_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_initL(lean_object* v_E_93_, lean_object* v_inst_94_, lean_object* v_n_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lp_tree_Formalism_L2_Col_initL___redArg(v_n_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_initL___boxed(lean_object* v_E_97_, lean_object* v_inst_98_, lean_object* v_n_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_tree_Formalism_L2_Col_initL(v_E_97_, v_inst_98_, v_n_99_);
lean_dec_ref(v_inst_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast___redArg___lam__0(lean_object* v_toZero_101_, lean_object* v_i_102_){
_start:
{
lean_inc(v_toZero_101_);
return v_toZero_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast___redArg___lam__0___boxed(lean_object* v_toZero_103_, lean_object* v_i_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_tree_Formalism_L2_Col_eLast___redArg___lam__0(v_toZero_103_, v_i_104_);
lean_dec(v_i_104_);
lean_dec(v_toZero_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast___redArg(lean_object* v_inst_106_, lean_object* v_n_107_, lean_object* v_j_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_toSemiring_111_; lean_object* v___x_112_; lean_object* v_toZero_113_; lean_object* v___x_114_; lean_object* v_toRing_115_; lean_object* v___x_116_; lean_object* v_toAddMonoidWithOne_117_; lean_object* v_toOne_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_109_ = lp_mathlib_Field_toSemifield___redArg(v_inst_106_);
v___x_110_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_109_);
v_toSemiring_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc_ref(v_toSemiring_111_);
lean_dec_ref(v___x_110_);
v___x_112_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_111_);
v_toZero_113_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_toZero_113_);
lean_dec_ref(v___x_112_);
v___x_114_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_106_);
v_toRing_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc_ref(v_toRing_115_);
lean_dec_ref(v___x_114_);
v___x_116_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_115_);
v_toAddMonoidWithOne_117_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_toAddMonoidWithOne_117_);
lean_dec_ref(v___x_116_);
v_toOne_118_ = lean_ctor_get(v_toAddMonoidWithOne_117_, 2);
lean_inc(v_toOne_118_);
lean_dec_ref(v_toAddMonoidWithOne_117_);
v___f_119_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_eLast___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v_toZero_113_);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_n_107_, v___x_120_);
v___x_122_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_122_, 0, v___x_121_);
v___x_123_ = lp_mathlib_Pi_single___redArg(v___f_119_, v___x_122_, v_n_107_, v_toOne_118_, v_j_108_);
lean_dec(v_toOne_118_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eLast(lean_object* v_E_124_, lean_object* v_inst_125_, lean_object* v_n_126_, lean_object* v_j_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lp_tree_Formalism_L2_Col_eLast___redArg(v_inst_125_, v_n_126_, v_j_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_z0___redArg(lean_object* v_inst_129_, lean_object* v_n_130_, lean_object* v_pi_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_toSemiring_135_; lean_object* v___x_136_; lean_object* v_toMul_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_133_ = lp_mathlib_Field_toSemifield___redArg(v_inst_129_);
v___x_134_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_133_);
v_toSemiring_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_toSemiring_135_);
lean_dec_ref(v___x_134_);
v___x_136_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_135_);
v_toMul_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_toMul_137_);
lean_dec_ref(v___x_136_);
v___x_138_ = lp_tree_Formalism_L2_Col_eLast___redArg(v_inst_129_, v_n_130_, v_a_132_);
v___x_139_ = lean_apply_2(v_toMul_137_, v_pi_131_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_z0(lean_object* v_E_140_, lean_object* v_inst_141_, lean_object* v_n_142_, lean_object* v_pi_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lp_tree_Formalism_L2_Col_z0___redArg(v_inst_141_, v_n_142_, v_pi_143_, v_a_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx___redArg(lean_object* v_n_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_sub(v_n_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx___redArg___boxed(lean_object* v_n_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = lp_tree_Formalism_L2_Col_lastIdx___redArg(v_n_149_);
lean_dec(v_n_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx(lean_object* v_n_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lp_tree_Formalism_L2_Col_lastIdx___redArg(v_n_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lastIdx___boxed(lean_object* v_n_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = lp_tree_Formalism_L2_Col_lastIdx(v_n_154_, v_inst_155_);
lean_dec(v_n_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_at(lean_object* v_E_157_, lean_object* v_inst_158_, lean_object* v_n_159_, lean_object* v_ST_160_, lean_object* v_SG_161_, lean_object* v_d_162_, lean_object* v_P_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_at___boxed(lean_object* v_E_165_, lean_object* v_inst_166_, lean_object* v_n_167_, lean_object* v_ST_168_, lean_object* v_SG_169_, lean_object* v_d_170_, lean_object* v_P_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = lp_tree_Formalism_L2_Col_Deco_at(v_E_165_, v_inst_166_, v_n_167_, v_ST_168_, v_SG_169_, v_d_170_, v_P_171_);
lean_dec_ref(v_d_170_);
lean_dec(v_SG_169_);
lean_dec(v_ST_168_);
lean_dec(v_n_167_);
lean_dec_ref(v_inst_166_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg___lam__0(lean_object* v_d_173_, lean_object* v_ga_174_, lean_object* v_P_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_f_177_; lean_object* v___x_178_; lean_object* v_toLinearMap_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_f_177_ = lean_ctor_get(v_d_173_, 1);
lean_inc(v_f_177_);
lean_dec_ref(v_d_173_);
v___x_178_ = lp_mathlib_LinearEquiv_symm___redArg(v_ga_174_);
v_toLinearMap_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_toLinearMap_179_);
lean_dec_ref(v___x_178_);
v___x_180_ = lean_apply_1(v_toLinearMap_179_, v_x_176_);
v___x_181_ = lean_apply_2(v_f_177_, v_P_175_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg___lam__1(lean_object* v___x_182_, lean_object* v_h_183_, lean_object* v_d_184_, lean_object* v_ga_185_, lean_object* v___x_186_, lean_object* v_w_187_, lean_object* v_x_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_val_194_; lean_object* v_be_195_; lean_object* v___x_196_; lean_object* v_toLinearMap_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_190_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_182_, v_w_187_);
v___x_191_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v___x_190_);
lean_dec_ref(v___x_190_);
v___x_192_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_191_);
v___x_193_ = lean_apply_1(v_h_183_, v_w_187_);
v_val_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_val_194_);
lean_dec_ref(v___x_193_);
v_be_195_ = lean_ctor_get(v_d_184_, 2);
lean_inc(v_be_195_);
lean_dec_ref(v_d_184_);
v___x_196_ = lp_mathlib_LinearEquiv_symm___redArg(v_ga_185_);
v_toLinearMap_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_toLinearMap_197_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_apply_1(v_toLinearMap_197_, v_x_188_);
v___x_199_ = lean_apply_2(v_be_195_, v_w_187_, v___x_198_);
v___x_200_ = lp_mathlib_Matrix_mulVec___redArg(v___x_192_, v___x_186_, v_val_194_, v___x_199_, v___y_189_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg(lean_object* v_inst_201_, lean_object* v_n_202_, lean_object* v_ga_203_, lean_object* v_h_204_, lean_object* v_d_205_){
_start:
{
lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_inc_ref(v_ga_203_);
lean_inc_ref(v_d_205_);
v___f_206_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Deco_act___redArg___lam__0), 4, 2);
lean_closure_set(v___f_206_, 0, v_d_205_);
lean_closure_set(v___f_206_, 1, v_ga_203_);
v___x_207_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_201_);
v___x_208_ = l_List_finRange(v_n_202_);
v___f_209_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Deco_act___redArg___lam__1), 8, 5);
lean_closure_set(v___f_209_, 0, v___x_207_);
lean_closure_set(v___f_209_, 1, v_h_204_);
lean_closure_set(v___f_209_, 2, v_d_205_);
lean_closure_set(v___f_209_, 3, v_ga_203_);
lean_closure_set(v___f_209_, 4, v___x_208_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___f_206_);
lean_ctor_set(v___x_211_, 2, v___f_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act(lean_object* v_E_212_, lean_object* v_inst_213_, lean_object* v_n_214_, lean_object* v_ST_215_, lean_object* v_SG_216_, lean_object* v_ga_217_, lean_object* v_h_218_, lean_object* v_d_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lp_tree_Formalism_L2_Col_Deco_act___redArg(v_inst_213_, v_n_214_, v_ga_217_, v_h_218_, v_d_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_act___boxed(lean_object* v_E_221_, lean_object* v_inst_222_, lean_object* v_n_223_, lean_object* v_ST_224_, lean_object* v_SG_225_, lean_object* v_ga_226_, lean_object* v_h_227_, lean_object* v_d_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = lp_tree_Formalism_L2_Col_Deco_act(v_E_221_, v_inst_222_, v_n_223_, v_ST_224_, v_SG_225_, v_ga_226_, v_h_227_, v_d_228_);
lean_dec(v_SG_225_);
lean_dec(v_ST_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia___redArg___lam__0(lean_object* v_c_230_, lean_object* v_inst_231_, lean_object* v_f_232_, lean_object* v_P_233_, lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; lean_object* v_toCommRing_236_; lean_object* v_toSemiring_237_; lean_object* v_toMonoid_238_; lean_object* v_val_239_; lean_object* v_toSemigroup_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_235_ = lean_apply_1(v_c_230_, v_P_233_);
v_toCommRing_236_ = lean_ctor_get(v_inst_231_, 0);
lean_inc_ref(v_toCommRing_236_);
lean_dec_ref(v_inst_231_);
v_toSemiring_237_ = lean_ctor_get(v_toCommRing_236_, 0);
lean_inc_ref(v_toSemiring_237_);
lean_dec_ref(v_toCommRing_236_);
v_toMonoid_238_ = lean_ctor_get(v_toSemiring_237_, 1);
lean_inc_ref(v_toMonoid_238_);
lean_dec_ref(v_toSemiring_237_);
v_val_239_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_239_);
lean_dec_ref(v___x_235_);
v_toSemigroup_240_ = lean_ctor_get(v_toMonoid_238_, 0);
lean_inc(v_toSemigroup_240_);
lean_dec_ref(v_toMonoid_238_);
v___x_241_ = lean_apply_2(v_f_232_, v_P_233_, v_x_234_);
v___x_242_ = lean_apply_2(v_toSemigroup_240_, v_val_239_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia___redArg(lean_object* v_inst_243_, lean_object* v_c_244_, lean_object* v_d_245_){
_start:
{
lean_object* v_N_246_; lean_object* v_f_247_; lean_object* v_be_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_N_246_ = lean_ctor_get(v_d_245_, 0);
v_f_247_ = lean_ctor_get(v_d_245_, 1);
v_be_248_ = lean_ctor_get(v_d_245_, 2);
v_isSharedCheck_256_ = !lean_is_exclusive(v_d_245_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v_d_245_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_be_248_);
lean_inc(v_f_247_);
lean_inc(v_N_246_);
lean_dec(v_d_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___f_252_; lean_object* v___x_254_; 
v___f_252_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Deco_dia___redArg___lam__0), 5, 3);
lean_closure_set(v___f_252_, 0, v_c_244_);
lean_closure_set(v___f_252_, 1, v_inst_243_);
lean_closure_set(v___f_252_, 2, v_f_247_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v___f_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_N_246_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___f_252_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_be_248_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia(lean_object* v_E_257_, lean_object* v_inst_258_, lean_object* v_n_259_, lean_object* v_ST_260_, lean_object* v_SG_261_, lean_object* v_c_262_, lean_object* v_d_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lp_tree_Formalism_L2_Col_Deco_dia___redArg(v_inst_258_, v_c_262_, v_d_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dia___boxed(lean_object* v_E_265_, lean_object* v_inst_266_, lean_object* v_n_267_, lean_object* v_ST_268_, lean_object* v_SG_269_, lean_object* v_c_270_, lean_object* v_d_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = lp_tree_Formalism_L2_Col_Deco_dia(v_E_265_, v_inst_266_, v_n_267_, v_ST_268_, v_SG_269_, v_c_270_, v_d_271_);
lean_dec(v_SG_269_);
lean_dec(v_ST_268_);
lean_dec(v_n_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_kerAt(lean_object* v_E_273_, lean_object* v_inst_274_, lean_object* v_n_275_, lean_object* v_ST_276_, lean_object* v_SG_277_, lean_object* v_d_278_, lean_object* v_P_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_kerAt___boxed(lean_object* v_E_281_, lean_object* v_inst_282_, lean_object* v_n_283_, lean_object* v_ST_284_, lean_object* v_SG_285_, lean_object* v_d_286_, lean_object* v_P_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lp_tree_Formalism_L2_Col_Deco_kerAt(v_E_281_, v_inst_282_, v_n_283_, v_ST_284_, v_SG_285_, v_d_286_, v_P_287_);
lean_dec_ref(v_d_286_);
lean_dec(v_SG_285_);
lean_dec(v_ST_284_);
lean_dec(v_n_283_);
lean_dec_ref(v_inst_282_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_L(lean_object* v_E_289_, lean_object* v_inst_290_, lean_object* v_n_291_, lean_object* v_ST_292_, lean_object* v_SG_293_, lean_object* v_d_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_L___boxed(lean_object* v_E_296_, lean_object* v_inst_297_, lean_object* v_n_298_, lean_object* v_ST_299_, lean_object* v_SG_300_, lean_object* v_d_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = lp_tree_Formalism_L2_Col_Deco_L(v_E_296_, v_inst_297_, v_n_298_, v_ST_299_, v_SG_300_, v_d_301_);
lean_dec_ref(v_d_301_);
lean_dec(v_SG_300_);
lean_dec(v_ST_299_);
lean_dec(v_n_298_);
lean_dec_ref(v_inst_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Lsh(lean_object* v_E_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_n_306_, lean_object* v_ST_307_, lean_object* v_SG_308_, lean_object* v_d_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_box(0);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Lsh___boxed(lean_object* v_E_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_n_314_, lean_object* v_ST_315_, lean_object* v_SG_316_, lean_object* v_d_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = lp_tree_Formalism_L2_Col_Deco_Lsh(v_E_311_, v_inst_312_, v_inst_313_, v_n_314_, v_ST_315_, v_SG_316_, v_d_317_);
lean_dec_ref(v_d_317_);
lean_dec(v_SG_316_);
lean_dec(v_ST_315_);
lean_dec(v_n_314_);
lean_dec(v_inst_313_);
lean_dec_ref(v_inst_312_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat(lean_object* v_E_319_, lean_object* v_inst_320_, lean_object* v_n_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___boxed(lean_object* v_E_323_, lean_object* v_inst_324_, lean_object* v_n_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = lp_tree_Formalism_L2_Col_stdLat(v_E_323_, v_inst_324_, v_n_325_);
lean_dec(v_n_325_);
lean_dec_ref(v_inst_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upA(lean_object* v_E_327_, lean_object* v_inst_328_, lean_object* v_n_329_, lean_object* v_P_330_, lean_object* v_N_331_, lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upA___boxed(lean_object* v_E_334_, lean_object* v_inst_335_, lean_object* v_n_336_, lean_object* v_P_337_, lean_object* v_N_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = lp_tree_Formalism_L2_Col_upA(v_E_334_, v_inst_335_, v_n_336_, v_P_337_, v_N_338_, v_x_339_);
lean_dec(v_x_339_);
lean_dec(v_n_336_);
lean_dec_ref(v_inst_335_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upN(lean_object* v_E_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_n_344_, lean_object* v_P_345_, lean_object* v_N_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_upN___boxed(lean_object* v_E_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_n_352_, lean_object* v_P_353_, lean_object* v_N_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = lp_tree_Formalism_L2_Col_upN(v_E_349_, v_inst_350_, v_inst_351_, v_n_352_, v_P_353_, v_N_354_, v_x_355_);
lean_dec(v_x_355_);
lean_dec(v_n_352_);
lean_dec(v_inst_351_);
lean_dec_ref(v_inst_350_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dnN(lean_object* v_E_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_n_360_, lean_object* v_ST_361_, lean_object* v_SG_362_, lean_object* v_d_363_, lean_object* v_P_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_dnN___boxed(lean_object* v_E_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_n_369_, lean_object* v_ST_370_, lean_object* v_SG_371_, lean_object* v_d_372_, lean_object* v_P_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = lp_tree_Formalism_L2_Col_Deco_dnN(v_E_366_, v_inst_367_, v_inst_368_, v_n_369_, v_ST_370_, v_SG_371_, v_d_372_, v_P_373_);
lean_dec_ref(v_d_372_);
lean_dec(v_SG_371_);
lean_dec(v_ST_370_);
lean_dec(v_n_369_);
lean_dec(v_inst_368_);
lean_dec_ref(v_inst_367_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_tilN(lean_object* v_E_375_, lean_object* v_inst_376_, lean_object* v_n_377_, lean_object* v_N_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_tilN___boxed(lean_object* v_E_380_, lean_object* v_inst_381_, lean_object* v_n_382_, lean_object* v_N_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = lp_tree_Formalism_L2_Col_tilN(v_E_380_, v_inst_381_, v_n_382_, v_N_383_);
lean_dec(v_n_382_);
lean_dec_ref(v_inst_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___redArg___lam__0(lean_object* v_inst_385_, lean_object* v_n_386_, lean_object* v_a_387_, lean_object* v_d_388_){
_start:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; 
v_fst_389_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v_a_387_);
v___x_391_ = lp_tree_Formalism_L2_Col_Deco_act___redArg(v_inst_385_, v_n_386_, v_fst_389_, v_snd_390_, v_d_388_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___redArg(lean_object* v_inst_392_, lean_object* v_n_393_){
_start:
{
lean_object* v___f_394_; 
v___f_394_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_394_, 0, v_inst_392_);
lean_closure_set(v___f_394_, 1, v_n_393_);
return v___f_394_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet(lean_object* v_E_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_n_399_, lean_object* v_ST_400_, lean_object* v_SG_401_){
_start:
{
lean_object* v___f_402_; 
v___f_402_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_402_, 0, v_inst_396_);
lean_closure_set(v___f_402_, 1, v_n_399_);
return v___f_402_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet___boxed(lean_object* v_E_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_n_407_, lean_object* v_ST_408_, lean_object* v_SG_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGDecoSet(v_E_403_, v_inst_404_, v_inst_405_, v_inst_406_, v_n_407_, v_ST_408_, v_SG_409_);
lean_dec(v_SG_409_);
lean_dec(v_ST_408_);
lean_dec(v_inst_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_dia___redArg(lean_object* v_inst_411_, lean_object* v_c_412_, lean_object* v_d_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lp_tree_Formalism_L2_Col_Deco_dia___redArg(v_inst_411_, v_c_412_, v_d_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_dia(lean_object* v_E_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_n_419_, lean_object* v_ST_420_, lean_object* v_SG_421_, lean_object* v_c_422_, lean_object* v_d_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lp_tree_Formalism_L2_Col_Deco_dia___redArg(v_inst_416_, v_c_422_, v_d_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_dia___boxed(lean_object* v_E_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_n_429_, lean_object* v_ST_430_, lean_object* v_SG_431_, lean_object* v_c_432_, lean_object* v_d_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = lp_tree_Formalism_L2_Col_DecoSet_dia(v_E_425_, v_inst_426_, v_inst_427_, v_inst_428_, v_n_429_, v_ST_430_, v_SG_431_, v_c_432_, v_d_433_);
lean_dec(v_SG_431_);
lean_dec(v_ST_430_);
lean_dec(v_n_429_);
lean_dec(v_inst_428_);
return v_res_434_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_DualOrthSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_NeighbourConstruct(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementB(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(uint8_t builtin) {
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
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_DualOrthSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_NeighbourConstruct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
