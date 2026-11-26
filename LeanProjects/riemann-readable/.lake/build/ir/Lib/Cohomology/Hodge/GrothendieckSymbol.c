// Lean compiler output
// Module: Lib.Cohomology.Hodge.GrothendieckSymbol
// Imports: public import Init public meta import Init public import Lib.Cohomology.Hodge.DepthVanishing public import Lib.General.Groups.CongruenceSubgroups public import Lib.PadicComparison.HodgeTate.ExtCocycles
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
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_Pi_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_AddZeroClass_toAddZero___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_CliffordAlgebra_instAlgebra___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ULift_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_freeAb___redArg();
lean_object* lp_GRH_New_Variety_abTensor___redArg();
lean_object* lp_GRH_New_Variety_exteriorAlg___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_comp___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_moduleCoeff___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_snd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_exteriorPower_00_u03b9Multi___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_freeAb_desc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_FreeAbelianGroup_of___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Algebra_id___redArg(lean_object*);
lean_object* lp_mathlib_FreeAlgebra_instSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_tmul___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_affineSpace___redArg();
lean_object* lp_GRH_New_Variety_HodgeTest_sqZeroExt___redArg();
lean_object* lp_GRH_New_Variety_instCategoryHodgeTest___redArg();
lean_object* lp_GRH_New_Variety_homReprEquiv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_ulift___redArg();
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_snoc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_abCoker_desc___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_detCochain___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_detCochain___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_detCochain___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_detCochain___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Variety_detCochain___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_detCochain___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_detCochain___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Variety_detCochain___redArg___closed__1_value;
static const lean_ctor_object lp_GRH_New_Variety_detCochain___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GRH_New_Variety_detCochain___redArg___closed__1_value),((lean_object*)&lp_GRH_New_Variety_detCochain___redArg___closed__0_value)}};
static const lean_object* lp_GRH_New_Variety_detCochain___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Variety_detCochain___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCocycle___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCocycle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCocycle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_volumeForm___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_TrivSqZeroExt_snd___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Variety_volumeForm___redArg___lam__1___closed__0 = (const lean_object*)&lp_GRH_New_Variety_volumeForm___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_volumeForm___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_volumeForm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_volumeForm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_formOfExteriorPower___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_formOfExteriorPower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_formOfExteriorPower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_dropLast___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_dropLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_dropLast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__2;
static lean_once_cell_t lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__3;
static lean_once_cell_t lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__4;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Variety_jouanolouRel___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel(lean_object* v_k_5_, lean_object* v_inst_6_, lean_object* v_d_7_, lean_object* v_V_8_, lean_object* v_f_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jouanolouRel___boxed(lean_object* v_k_11_, lean_object* v_inst_12_, lean_object* v_d_13_, lean_object* v_V_14_, lean_object* v_f_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_Variety_jouanolouRel(v_k_11_, v_inst_12_, v_d_13_, v_V_14_, v_f_15_);
lean_dec(v_f_15_);
lean_dec_ref(v_V_14_);
lean_dec(v_d_13_);
lean_dec_ref(v_inst_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0(lean_object* v___x_17_, lean_object* v_i_18_){
_start:
{
lean_inc_ref(v___x_17_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0___boxed(lean_object* v___x_19_, lean_object* v_i_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0(v___x_19_, v_i_20_);
lean_dec(v_i_20_);
lean_dec_ref(v___x_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__1(lean_object* v_toZero_22_, lean_object* v_x_23_){
_start:
{
lean_inc(v_toZero_22_);
return v_toZero_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__1___boxed(lean_object* v_toZero_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__1(v_toZero_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec(v_toZero_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg(lean_object* v_c_27_){
_start:
{
lean_object* v_baseAlg_28_; lean_object* v_commRing_29_; lean_object* v_toSemiring_30_; lean_object* v___x_31_; lean_object* v_toAddCommMonoid_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v_toZero_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v_toSMul_42_; lean_object* v___f_43_; 
v_baseAlg_28_ = lean_ctor_get(v_c_27_, 0);
lean_inc_ref(v_baseAlg_28_);
lean_dec_ref(v_c_27_);
v_commRing_29_ = lean_ctor_get(v_baseAlg_28_, 0);
lean_inc_ref(v_commRing_29_);
lean_dec_ref(v_baseAlg_28_);
v_toSemiring_30_ = lean_ctor_get(v_commRing_29_, 0);
v___x_31_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_commRing_29_);
v_toAddCommMonoid_32_ = lean_ctor_get(v_toSemiring_30_, 0);
v___f_33_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_33_, 0, v___x_31_);
v___x_34_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_33_);
v___x_35_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_32_);
v___x_36_ = lp_mathlib_AddZeroClass_toAddZero___redArg(v___x_35_);
v_toZero_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_toZero_37_);
lean_dec_ref(v___x_36_);
v___x_38_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_30_);
v___x_39_ = lp_mathlib_Pi_Function_module___redArg(v___x_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_40_, 0, v_toZero_37_);
v___x_41_ = lp_mathlib_CliffordAlgebra_instAlgebra___redArg(v_commRing_29_, v___x_34_, v___x_39_, v___f_40_);
v_toSMul_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_toSMul_42_);
lean_dec_ref(v___x_41_);
v___f_43_ = lean_alloc_closure((void*)(lp_mathlib_ULift_smul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_43_, 0, v_toSMul_42_);
return v___f_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff(lean_object* v_k_44_, lean_object* v_inst_45_, lean_object* v_c_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg(v_c_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___boxed(lean_object* v_k_48_, lean_object* v_inst_49_, lean_object* v_c_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff(v_k_48_, v_inst_49_, v_c_50_);
lean_dec_ref(v_inst_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__0(lean_object* v_X_52_, lean_object* v_Y_53_, lean_object* v_f_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_apply_1(v_f_54_, v___y_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__0___boxed(lean_object* v_X_57_, lean_object* v_Y_58_, lean_object* v_f_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_GRH_New_Variety_detCochain___redArg___lam__0(v_X_57_, v_Y_58_, v_f_59_, v___y_60_);
lean_dec_ref(v_Y_58_);
lean_dec_ref(v_X_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__1(lean_object* v_M_62_){
_start:
{
lean_object* v_isRing_63_; lean_object* v_isAlgebra_64_; lean_object* v___x_65_; lean_object* v_toSMul_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_isRing_63_ = lean_ctor_get(v_M_62_, 0);
lean_inc_ref(v_isRing_63_);
v_isAlgebra_64_ = lean_ctor_get(v_M_62_, 1);
lean_inc_ref(v_isAlgebra_64_);
lean_dec_ref(v_M_62_);
v___x_65_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_isRing_63_);
lean_dec_ref(v_isRing_63_);
v_toSMul_66_ = lean_ctor_get(v_isAlgebra_64_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_isAlgebra_64_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v_isAlgebra_64_, 1);
lean_dec(v_unused_74_);
v___x_68_ = v_isAlgebra_64_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_toSMul_66_);
lean_dec(v_isAlgebra_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_toSMul_66_);
lean_ctor_set(v___x_68_, 0, v___x_65_);
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_toSMul_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__2(lean_object* v_snd_75_, lean_object* v_i_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_apply_2(v_snd_75_, v_i_76_, v___y_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg___lam__3(lean_object* v_d_79_, lean_object* v___x_80_, lean_object* v_00_u03c9_81_, lean_object* v_c_82_, lean_object* v_t_83_){
_start:
{
lean_object* v_baseAlg_84_; lean_object* v_commRing_85_; lean_object* v_toSemiring_86_; lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_399__overap_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_baseAlg_84_ = lean_ctor_get(v_c_82_, 0);
v_commRing_85_ = lean_ctor_get(v_baseAlg_84_, 0);
v_toSemiring_86_ = lean_ctor_get(v_commRing_85_, 0);
lean_inc_ref(v_toSemiring_86_);
v_fst_87_ = lean_ctor_get(v_t_83_, 0);
lean_inc(v_fst_87_);
v_snd_88_ = lean_ctor_get(v_t_83_, 1);
lean_inc(v_snd_88_);
lean_dec_ref(v_t_83_);
v___f_89_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_detCochain___redArg___lam__2), 3, 1);
lean_closure_set(v___f_89_, 0, v_snd_88_);
v___x_90_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_90_, 0, v_d_79_);
lean_inc_ref(v_commRing_85_);
v___x_399__overap_91_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___x_90_, v___x_80_, v_commRing_85_);
v___x_92_ = lean_apply_1(v___x_399__overap_91_, v___f_89_);
v___x_93_ = lp_mathlib_FreeAbelianGroup_of___redArg(v_fst_87_);
v___x_94_ = lean_apply_2(v_00_u03c9_81_, v_c_82_, v___x_93_);
v___x_95_ = lp_mathlib_Algebra_id___redArg(v_toSemiring_86_);
v___x_96_ = lp_mathlib_FreeAlgebra_instSMul___redArg___lam__0(v___x_95_, v___x_92_, v___x_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___redArg(lean_object* v_inst_102_, lean_object* v_d_103_, lean_object* v_00_u03c9_104_){
_start:
{
lean_object* v_toCommRing_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___f_112_; 
v_toCommRing_105_ = lean_ctor_get(v_inst_102_, 0);
lean_inc_ref(v_toCommRing_105_);
lean_dec_ref(v_inst_102_);
v___x_106_ = lp_GRH_New_Variety_exteriorAlg___redArg(v_toCommRing_105_);
v___x_107_ = ((lean_object*)(lp_GRH_New_Variety_detCochain___redArg___closed__2));
v___x_108_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_106_, v___x_107_);
v___x_109_ = lp_GRH_New_Variety_moduleCoeff___redArg(v___x_108_);
lean_inc(v_d_103_);
v___x_110_ = l_List_finRange(v_d_103_);
v___f_111_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_detCochain___redArg___lam__3), 5, 3);
lean_closure_set(v___f_111_, 0, v_d_103_);
lean_closure_set(v___f_111_, 1, v___x_110_);
lean_closure_set(v___f_111_, 2, v_00_u03c9_104_);
v___f_112_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_freeAb_desc___redArg___lam__0), 4, 2);
lean_closure_set(v___f_112_, 0, v___x_109_);
lean_closure_set(v___f_112_, 1, v___f_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain(lean_object* v_k_113_, lean_object* v_inst_114_, lean_object* v_d_115_, lean_object* v_V_116_, lean_object* v_R_117_, lean_object* v_00_u03c9_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_GRH_New_Variety_detCochain___redArg(v_inst_114_, v_d_115_, v_00_u03c9_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCochain___boxed(lean_object* v_k_120_, lean_object* v_inst_121_, lean_object* v_d_122_, lean_object* v_V_123_, lean_object* v_R_124_, lean_object* v_00_u03c9_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_GRH_New_Variety_detCochain(v_k_120_, v_inst_121_, v_d_122_, v_V_123_, v_R_124_, v_00_u03c9_125_);
lean_dec_ref(v_V_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCocycle___redArg(lean_object* v_inst_127_, lean_object* v_d_128_, lean_object* v_00_u03c9_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___f_131_; 
v___x_130_ = lp_GRH_New_Variety_detCochain___redArg(v_inst_127_, v_d_128_, v_00_u03c9_129_);
v___f_131_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abCoker_desc___redArg___lam__0), 3, 1);
lean_closure_set(v___f_131_, 0, v___x_130_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCocycle(lean_object* v_k_132_, lean_object* v_inst_133_, lean_object* v_d_134_, lean_object* v_V_135_, lean_object* v_f_136_, lean_object* v_00_u03c9_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_GRH_New_Variety_detCocycle___redArg(v_inst_133_, v_d_134_, v_00_u03c9_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_detCocycle___boxed(lean_object* v_k_139_, lean_object* v_inst_140_, lean_object* v_d_141_, lean_object* v_V_142_, lean_object* v_f_143_, lean_object* v_00_u03c9_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = lp_GRH_New_Variety_detCocycle(v_k_139_, v_inst_140_, v_d_141_, v_V_142_, v_f_143_, v_00_u03c9_144_);
lean_dec(v_f_143_);
lean_dec_ref(v_V_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_volumeForm___redArg___lam__1(lean_object* v_d_147_, lean_object* v_c_148_, lean_object* v_v_149_){
_start:
{
lean_object* v_baseAlg_150_; lean_object* v_commRing_151_; lean_object* v___x_152_; lean_object* v_toSemiring_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_116__overap_160_; lean_object* v___x_161_; 
v_baseAlg_150_ = lean_ctor_get(v_c_148_, 0);
lean_inc_ref(v_baseAlg_150_);
lean_dec_ref(v_c_148_);
v_commRing_151_ = lean_ctor_get(v_baseAlg_150_, 0);
lean_inc_ref(v_commRing_151_);
lean_dec_ref(v_baseAlg_150_);
v___x_152_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_commRing_151_);
v_toSemiring_153_ = lean_ctor_get(v_commRing_151_, 0);
v___f_154_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_instModuleCarrierBaseAlgCarrierObjHodgeTestAddCommGrpCatHodgeCoeff___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_154_, 0, v___x_152_);
v___x_155_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_153_);
v___x_156_ = lp_mathlib_Pi_Function_module___redArg(v___x_155_);
v___x_157_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_154_);
v___x_158_ = ((lean_object*)(lp_GRH_New_Variety_volumeForm___redArg___lam__1___closed__0));
v___x_159_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_159_, 0, lean_box(0));
lean_closure_set(v___x_159_, 1, lean_box(0));
lean_closure_set(v___x_159_, 2, lean_box(0));
lean_closure_set(v___x_159_, 3, v___x_158_);
lean_closure_set(v___x_159_, 4, v_v_149_);
v___x_116__overap_160_ = lp_mathlib_exteriorPower_00_u03b9Multi___redArg(v_commRing_151_, v_d_147_, v___x_157_, v___x_156_);
v___x_161_ = lean_apply_1(v___x_116__overap_160_, v___x_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_volumeForm___redArg(lean_object* v_inst_162_, lean_object* v_d_163_){
_start:
{
lean_object* v_toCommRing_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___f_170_; 
v_toCommRing_164_ = lean_ctor_get(v_inst_162_, 0);
lean_inc_ref(v_toCommRing_164_);
lean_dec_ref(v_inst_162_);
v___f_165_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_volumeForm___redArg___lam__1), 3, 1);
lean_closure_set(v___f_165_, 0, v_d_163_);
v___x_166_ = lp_GRH_New_Variety_exteriorAlg___redArg(v_toCommRing_164_);
v___x_167_ = ((lean_object*)(lp_GRH_New_Variety_detCochain___redArg___closed__2));
v___x_168_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_166_, v___x_167_);
v___x_169_ = lp_GRH_New_Variety_moduleCoeff___redArg(v___x_168_);
v___f_170_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_freeAb_desc___redArg___lam__0), 4, 2);
lean_closure_set(v___f_170_, 0, v___x_169_);
lean_closure_set(v___f_170_, 1, v___f_165_);
return v___f_170_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_volumeForm(lean_object* v_k_171_, lean_object* v_inst_172_, lean_object* v_d_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lp_GRH_New_Variety_volumeForm___redArg(v_inst_172_, v_d_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus___redArg(){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus___redArg___boxed(lean_object* v___dummy_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_GRH_New_Variety_unimodularLocus___redArg();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus(lean_object* v_k_179_, lean_object* v_inst_180_, lean_object* v_d_181_, lean_object* v_c_182_, lean_object* v_g_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularLocus___boxed(lean_object* v_k_185_, lean_object* v_inst_186_, lean_object* v_d_187_, lean_object* v_c_188_, lean_object* v_g_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_GRH_New_Variety_unimodularLocus(v_k_185_, v_inst_186_, v_d_187_, v_c_188_, v_g_189_);
lean_dec_ref(v_g_189_);
lean_dec_ref(v_c_188_);
lean_dec(v_d_187_);
lean_dec_ref(v_inst_186_);
return v_res_190_;
}
}
static lean_object* _init_lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__0(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lp_GRH_New_Variety_instCategoryHodgeTest___redArg();
return v___x_191_;
}
}
static lean_object* _init_lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__1(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lp_mathlib_Equiv_ulift___redArg();
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_formOfExteriorPower___redArg(lean_object* v_inst_193_, lean_object* v_c_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_toCommRing_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_toFun_206_; lean_object* v___x_207_; 
v_toCommRing_196_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toCommRing_196_);
lean_dec_ref(v_inst_193_);
v___x_197_ = lean_obj_once(&lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__0, &lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__0_once, _init_lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__0);
v___x_198_ = lp_GRH_New_Variety_exteriorAlg___redArg(v_toCommRing_196_);
v___x_199_ = ((lean_object*)(lp_GRH_New_Variety_detCochain___redArg___closed__2));
v___x_200_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_198_, v___x_199_);
v___x_201_ = lp_GRH_New_Variety_moduleCoeff___redArg(v___x_200_);
v___x_202_ = lp_GRH_New_Variety_homReprEquiv___redArg(v___x_197_, v_c_194_, v___x_201_);
v___x_203_ = lean_obj_once(&lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__1, &lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__1_once, _init_lp_GRH_New_Variety_formOfExteriorPower___redArg___closed__1);
v___x_204_ = lp_mathlib_Equiv_trans___redArg(v___x_202_, v___x_203_);
v___x_205_ = lp_mathlib_Equiv_symm___redArg(v___x_204_);
v_toFun_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_toFun_206_);
lean_dec_ref(v___x_205_);
v___x_207_ = lean_apply_1(v_toFun_206_, v_x_195_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_formOfExteriorPower(lean_object* v_k_208_, lean_object* v_inst_209_, lean_object* v_d_210_, lean_object* v_c_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lp_GRH_New_Variety_formOfExteriorPower___redArg(v_inst_209_, v_c_211_, v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_formOfExteriorPower___boxed(lean_object* v_k_214_, lean_object* v_inst_215_, lean_object* v_d_216_, lean_object* v_c_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = lp_GRH_New_Variety_formOfExteriorPower(v_k_214_, v_inst_215_, v_d_216_, v_c_217_, v_x_218_);
lean_dec(v_d_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter___redArg(lean_object* v_x_220_, lean_object* v_h__1_221_){
_start:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_224_; 
v_fst_222_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_fst_222_);
v_snd_223_ = lean_ctor_get(v_x_220_, 1);
lean_inc(v_snd_223_);
lean_dec_ref(v_x_220_);
v___x_224_ = lean_apply_2(v_h__1_221_, v_fst_222_, v_snd_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter(lean_object* v_k_225_, lean_object* v_inst_226_, lean_object* v_d_227_, lean_object* v_c_228_, lean_object* v_C_229_, lean_object* v_motive_230_, lean_object* v_x_231_, lean_object* v_h__1_232_){
_start:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_235_; 
v_fst_233_ = lean_ctor_get(v_x_231_, 0);
lean_inc(v_fst_233_);
v_snd_234_ = lean_ctor_get(v_x_231_, 1);
lean_inc(v_snd_234_);
lean_dec_ref(v_x_231_);
v___x_235_ = lean_apply_2(v_h__1_232_, v_fst_233_, v_snd_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter___boxed(lean_object* v_k_236_, lean_object* v_inst_237_, lean_object* v_d_238_, lean_object* v_c_239_, lean_object* v_C_240_, lean_object* v_motive_241_, lean_object* v_x_242_, lean_object* v_h__1_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_smul__grothendieckSymbol__eq__fractionClass_match__1__1_splitter(v_k_236_, v_inst_237_, v_d_238_, v_c_239_, v_C_240_, v_motive_241_, v_x_242_, v_h__1_243_);
lean_dec_ref(v_C_240_);
lean_dec_ref(v_c_239_);
lean_dec(v_d_238_);
lean_dec_ref(v_inst_237_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___redArg___lam__0(lean_object* v___x_245_, lean_object* v_d_246_, lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_fst_250_ = lean_ctor_get(v___y_248_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v___y_248_, 1);
lean_inc(v_snd_251_);
lean_dec_ref(v___y_248_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_nat_mod(v___x_252_, v___x_245_);
v___x_254_ = lean_apply_1(v_snd_251_, v___x_253_);
v___x_255_ = lp_mathlib_Fin_snoc___redArg(v_d_246_, v_fst_250_, v___x_254_, v___y_249_);
lean_dec(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___redArg___lam__0___boxed(lean_object* v___x_256_, lean_object* v_d_257_, lean_object* v_x_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = lp_GRH_New_Variety_affineSpace_snoc___redArg___lam__0(v___x_256_, v_d_257_, v_x_258_, v___y_259_, v___y_260_);
lean_dec_ref(v_x_258_);
lean_dec(v_d_257_);
lean_dec(v___x_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___redArg(lean_object* v_d_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___f_264_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___f_264_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_affineSpace_snoc___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_264_, 0, v___x_263_);
lean_closure_set(v___f_264_, 1, v_d_262_);
return v___f_264_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc(lean_object* v_k_265_, lean_object* v_inst_266_, lean_object* v_d_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lp_GRH_New_Variety_affineSpace_snoc___redArg(v_d_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_affineSpace_snoc___boxed(lean_object* v_k_269_, lean_object* v_inst_270_, lean_object* v_d_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = lp_GRH_New_Variety_affineSpace_snoc(v_k_269_, v_inst_270_, v_d_271_);
lean_dec_ref(v_inst_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup___redArg(){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup___redArg___boxed(lean_object* v___dummy_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = lp_GRH_New_Variety_unimodularSup___redArg();
return v_res_276_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup(lean_object* v_k_277_, lean_object* v_inst_278_, lean_object* v_d_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_unimodularSup___boxed(lean_object* v_k_281_, lean_object* v_inst_282_, lean_object* v_d_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_GRH_New_Variety_unimodularSup(v_k_281_, v_inst_282_, v_d_283_);
lean_dec(v_d_283_);
lean_dec_ref(v_inst_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel___redArg(){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel___redArg___boxed(lean_object* v___dummy_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lp_GRH_New_Variety_snocRel___redArg();
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel(lean_object* v_k_289_, lean_object* v_inst_290_, lean_object* v_d_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel___boxed(lean_object* v_k_293_, lean_object* v_inst_294_, lean_object* v_d_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = lp_GRH_New_Variety_snocRel(v_k_293_, v_inst_294_, v_d_295_);
lean_dec(v_d_295_);
lean_dec_ref(v_inst_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint___redArg(lean_object* v_t_297_){
_start:
{
lean_object* v_fst_298_; lean_object* v_fst_299_; 
v_fst_298_ = lean_ctor_get(v_t_297_, 0);
v_fst_299_ = lean_ctor_get(v_fst_298_, 0);
lean_inc(v_fst_299_);
return v_fst_299_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint___redArg___boxed(lean_object* v_t_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = lp_GRH_New_Variety_snocRel_firstPoint___redArg(v_t_300_);
lean_dec_ref(v_t_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint(lean_object* v_k_302_, lean_object* v_inst_303_, lean_object* v_d_304_, lean_object* v_c_305_, lean_object* v_m_306_, lean_object* v_t_307_){
_start:
{
lean_object* v_fst_308_; lean_object* v_fst_309_; 
v_fst_308_ = lean_ctor_get(v_t_307_, 0);
v_fst_309_ = lean_ctor_get(v_fst_308_, 0);
lean_inc(v_fst_309_);
return v_fst_309_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_firstPoint___boxed(lean_object* v_k_310_, lean_object* v_inst_311_, lean_object* v_d_312_, lean_object* v_c_313_, lean_object* v_m_314_, lean_object* v_t_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = lp_GRH_New_Variety_snocRel_firstPoint(v_k_310_, v_inst_311_, v_d_312_, v_c_313_, v_m_314_, v_t_315_);
lean_dec_ref(v_t_315_);
lean_dec(v_m_314_);
lean_dec_ref(v_c_313_);
lean_dec(v_d_312_);
lean_dec_ref(v_inst_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint___redArg(lean_object* v_t_317_){
_start:
{
lean_object* v_fst_318_; lean_object* v_snd_319_; 
v_fst_318_ = lean_ctor_get(v_t_317_, 0);
v_snd_319_ = lean_ctor_get(v_fst_318_, 1);
lean_inc(v_snd_319_);
return v_snd_319_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint___redArg___boxed(lean_object* v_t_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = lp_GRH_New_Variety_snocRel_lastPoint___redArg(v_t_320_);
lean_dec_ref(v_t_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint(lean_object* v_k_322_, lean_object* v_inst_323_, lean_object* v_d_324_, lean_object* v_c_325_, lean_object* v_m_326_, lean_object* v_t_327_){
_start:
{
lean_object* v_fst_328_; lean_object* v_snd_329_; 
v_fst_328_ = lean_ctor_get(v_t_327_, 0);
v_snd_329_ = lean_ctor_get(v_fst_328_, 1);
lean_inc(v_snd_329_);
return v_snd_329_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_lastPoint___boxed(lean_object* v_k_330_, lean_object* v_inst_331_, lean_object* v_d_332_, lean_object* v_c_333_, lean_object* v_m_334_, lean_object* v_t_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = lp_GRH_New_Variety_snocRel_lastPoint(v_k_330_, v_inst_331_, v_d_332_, v_c_333_, v_m_334_, v_t_335_);
lean_dec_ref(v_t_335_);
lean_dec(v_m_334_);
lean_dec_ref(v_c_333_);
lean_dec(v_d_332_);
lean_dec_ref(v_inst_331_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_dropLast___redArg(lean_object* v_t_337_){
_start:
{
lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v_fst_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_fst_338_ = lean_ctor_get(v_t_337_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_snd_339_);
lean_dec_ref(v_t_337_);
v_fst_340_ = lean_ctor_get(v_fst_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_fst_338_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_fst_338_, 1);
lean_dec(v_unused_349_);
v___x_342_ = v_fst_338_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_fst_340_);
lean_dec(v_fst_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___f_344_; lean_object* v___x_346_; 
v___f_344_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_detCochain___redArg___lam__2), 3, 1);
lean_closure_set(v___f_344_, 0, v_snd_339_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___f_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_fst_340_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___f_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_dropLast(lean_object* v_k_350_, lean_object* v_inst_351_, lean_object* v_d_352_, lean_object* v_c_353_, lean_object* v_m_354_, lean_object* v_t_355_, lean_object* v_hx_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lp_GRH_New_Variety_snocRel_dropLast___redArg(v_t_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_dropLast___boxed(lean_object* v_k_358_, lean_object* v_inst_359_, lean_object* v_d_360_, lean_object* v_c_361_, lean_object* v_m_362_, lean_object* v_t_363_, lean_object* v_hx_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = lp_GRH_New_Variety_snocRel_dropLast(v_k_358_, v_inst_359_, v_d_360_, v_c_361_, v_m_362_, v_t_363_, v_hx_364_);
lean_dec(v_m_362_);
lean_dec_ref(v_c_361_);
lean_dec(v_d_360_);
lean_dec_ref(v_inst_359_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___lam__2(lean_object* v_snd_366_, lean_object* v_i_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_apply_2(v_snd_366_, v_i_367_, v___y_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg___lam__0(lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v_d_372_, lean_object* v_inst_373_, lean_object* v_c_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_fst_376_; lean_object* v_snd_377_; lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_400_; 
v_fst_376_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_fst_376_);
v_snd_377_ = lean_ctor_get(v_x_375_, 1);
lean_inc(v_snd_377_);
lean_dec_ref(v_x_375_);
v_fst_378_ = lean_ctor_get(v_fst_376_, 0);
v_snd_379_ = lean_ctor_get(v_fst_376_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_fst_376_);
if (v_isSharedCheck_400_ == 0)
{
v___x_381_ = v_fst_376_;
v_isShared_382_ = v_isSharedCheck_400_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_378_);
lean_dec(v_fst_376_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_400_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_obj_383_; lean_object* v___x_384_; lean_object* v_toZSMul_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v_obj_383_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_obj_383_);
lean_dec_ref(v___x_370_);
lean_inc_ref(v_c_374_);
v___x_384_ = lean_apply_1(v_obj_383_, v_c_374_);
v_toZSMul_385_ = lean_ctor_get(v___x_384_, 3);
lean_inc(v_toZSMul_385_);
lean_dec_ref(v___x_384_);
v___f_386_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_snocRel_detTensor___redArg___lam__2), 3, 1);
lean_closure_set(v___f_386_, 0, v_snd_377_);
v___x_387_ = lean_nat_to_int(v___x_371_);
v___x_388_ = lean_int_neg(v___x_387_);
lean_dec(v___x_387_);
v___x_389_ = l_Int_pow(v___x_388_, v_d_372_);
lean_dec(v___x_388_);
lean_inc(v_d_372_);
lean_inc_ref(v_inst_373_);
v___x_390_ = lp_GRH_New_Variety_volumeForm___redArg(v_inst_373_, v_d_372_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___f_386_);
v___x_392_ = v___x_381_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_fst_378_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___f_386_);
v___x_392_ = v_reuseFailAlloc_399_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_523__overap_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_393_ = lp_mathlib_FreeAbelianGroup_of___redArg(v___x_392_);
v___x_523__overap_394_ = lp_GRH_New_Variety_detCochain___redArg(v_inst_373_, v_d_372_, v___x_390_);
v___x_395_ = lean_apply_2(v___x_523__overap_394_, v_c_374_, v___x_393_);
v___x_396_ = lean_apply_2(v_toZSMul_385_, v___x_389_, v___x_395_);
v___x_397_ = lp_mathlib_FreeAbelianGroup_of___redArg(v_snd_379_);
v___x_398_ = lp_mathlib_TensorProduct_tmul___redArg(v___x_396_, v___x_397_);
return v___x_398_;
}
}
}
}
static lean_object* _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__0(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lp_GRH_New_Variety_abTensor___redArg();
return v___x_401_;
}
}
static lean_object* _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__1(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lp_GRH_New_Variety_freeAb___redArg();
return v___x_402_;
}
}
static lean_object* _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__2(void){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lp_GRH_New_Variety_HodgeTest_sqZeroExt___redArg();
return v___x_403_;
}
}
static lean_object* _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__3(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lp_GRH_New_Variety_affineSpace___redArg();
return v___x_404_;
}
}
static lean_object* _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__4(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__3, &lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__3_once, _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__3);
v___x_406_ = lean_obj_once(&lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__2, &lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__2_once, _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__2);
v___x_407_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_406_, v___x_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor___redArg(lean_object* v_inst_408_, lean_object* v_d_409_){
_start:
{
lean_object* v_toCommRing_410_; lean_object* v___x_411_; lean_object* v_obj_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_obj_418_; lean_object* v___x_419_; lean_object* v_obj_420_; lean_object* v___x_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; 
v_toCommRing_410_ = lean_ctor_get(v_inst_408_, 0);
v___x_411_ = lean_obj_once(&lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__0, &lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__0_once, _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__0);
v_obj_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_toCommRing_410_);
v___x_413_ = lp_GRH_New_Variety_exteriorAlg___redArg(v_toCommRing_410_);
v___x_414_ = ((lean_object*)(lp_GRH_New_Variety_detCochain___redArg___closed__2));
v___x_415_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_413_, v___x_414_);
v___x_416_ = lp_GRH_New_Variety_moduleCoeff___redArg(v___x_415_);
lean_inc(v_obj_412_);
lean_inc_ref(v___x_416_);
v___x_417_ = lean_apply_1(v_obj_412_, v___x_416_);
v_obj_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_obj_418_);
lean_dec_ref(v___x_417_);
v___x_419_ = lean_obj_once(&lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__1, &lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__1_once, _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__1);
v_obj_420_ = lean_ctor_get(v___x_419_, 0);
v___x_421_ = lean_unsigned_to_nat(1u);
v___f_422_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_snocRel_detTensor___redArg___lam__0), 6, 4);
lean_closure_set(v___f_422_, 0, v___x_416_);
lean_closure_set(v___f_422_, 1, v___x_421_);
lean_closure_set(v___f_422_, 2, v_d_409_);
lean_closure_set(v___f_422_, 3, v_inst_408_);
v___x_423_ = lean_obj_once(&lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__4, &lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__4_once, _init_lp_GRH_New_Variety_snocRel_detTensor___redArg___closed__4);
lean_inc(v_obj_420_);
v___x_424_ = lean_apply_1(v_obj_420_, v___x_423_);
v___x_425_ = lean_apply_1(v_obj_418_, v___x_424_);
v___f_426_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_freeAb_desc___redArg___lam__0), 4, 2);
lean_closure_set(v___f_426_, 0, v___x_425_);
lean_closure_set(v___f_426_, 1, v___f_422_);
return v___f_426_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_snocRel_detTensor(lean_object* v_k_427_, lean_object* v_inst_428_, lean_object* v_d_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lp_GRH_New_Variety_snocRel_detTensor___redArg(v_inst_428_, v_d_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter___redArg(lean_object* v_x_431_, lean_object* v_h__1_432_){
_start:
{
lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_437_; 
v_fst_433_ = lean_ctor_get(v_x_431_, 0);
lean_inc(v_fst_433_);
v_snd_434_ = lean_ctor_get(v_x_431_, 1);
lean_inc(v_snd_434_);
lean_dec_ref(v_x_431_);
v_fst_435_ = lean_ctor_get(v_fst_433_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v_fst_433_, 1);
lean_inc(v_snd_436_);
lean_dec(v_fst_433_);
v___x_437_ = lean_apply_4(v_h__1_432_, v_fst_435_, v_snd_436_, v_snd_434_, lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter(lean_object* v_k_438_, lean_object* v_inst_439_, lean_object* v_d_440_, lean_object* v_c_441_, lean_object* v_motive_442_, lean_object* v_x_443_, lean_object* v_h__1_444_){
_start:
{
lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; 
v_fst_445_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_snd_446_);
lean_dec_ref(v_x_443_);
v_fst_447_ = lean_ctor_get(v_fst_445_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v_fst_445_, 1);
lean_inc(v_snd_448_);
lean_dec(v_fst_445_);
v___x_449_ = lean_apply_4(v_h__1_444_, v_fst_447_, v_snd_448_, v_snd_446_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter___boxed(lean_object* v_k_450_, lean_object* v_inst_451_, lean_object* v_d_452_, lean_object* v_c_453_, lean_object* v_motive_454_, lean_object* v_x_455_, lean_object* v_h__1_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = lp_GRH___private_Lib_Cohomology_Hodge_GrothendieckSymbol_0__New_Variety_snocRel_detTensor_match__1_splitter(v_k_450_, v_inst_451_, v_d_452_, v_c_453_, v_motive_454_, v_x_455_, v_h__1_456_);
lean_dec_ref(v_c_453_);
lean_dec(v_d_452_);
lean_dec_ref(v_inst_451_);
return v_res_457_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Hodge_DepthVanishing(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_CongruenceSubgroups(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_HodgeTate_ExtCocycles(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_Hodge_GrothendieckSymbol(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Hodge_DepthVanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Groups_CongruenceSubgroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_HodgeTate_ExtCocycles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
