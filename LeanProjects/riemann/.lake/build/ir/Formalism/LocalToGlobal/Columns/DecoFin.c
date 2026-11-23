// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.DecoFin
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.StdLatUnimodular public import Formalism.LocalToGlobal.Columns.BaseLemmas public import Formalism.HermitianLattices.FinalNeighbourConstruct public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_smulRight___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_tree_Formalism_L2_Col_incl___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_initL___redArg(lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_eLast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_ofLinearMap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_NumberField_RingOfIntegers_mapRingHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* l_Fin_lastCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_ring___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_evalMulHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MulHom_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cO___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjPrime_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjPrime_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extL___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_padM___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__4___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cO___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___f_2_; 
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_NumberField_RingOfIntegers_mapRingHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2_, 0, v_inst_1_);
return v___f_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cO(lean_object* v_E_3_, lean_object* v_inst_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_NumberField_RingOfIntegers_mapRingHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_inst_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cO___boxed(lean_object* v_E_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_L2_Col_cO(v_E_7_, v_inst_8_, v_inst_9_);
lean_dec_ref(v_inst_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjPrime_u2082(lean_object* v_E_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_P_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjPrime_u2082___boxed(lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_P_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_Col_conjPrime_u2082(v_E_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_P_21_);
lean_dec(v_inst_20_);
lean_dec_ref(v_inst_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extL___redArg___lam__0(lean_object* v_toAddCommMonoid_23_, lean_object* v___f_24_, lean_object* v___x_25_, lean_object* v___x_26_, lean_object* v___x_27_, lean_object* v___x_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_toAddSemigroup_31_; lean_object* v___x_244__overap_32_; lean_object* v___x_33_; lean_object* v___x_245__overap_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_toAddSemigroup_31_ = lean_ctor_get(v_toAddCommMonoid_23_, 0);
lean_inc(v_toAddSemigroup_31_);
lean_dec_ref(v_toAddCommMonoid_23_);
lean_inc(v___y_29_);
v___x_244__overap_32_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___f_24_, v___x_25_, v___y_29_);
lean_inc(v___y_30_);
v___x_33_ = lean_apply_1(v___x_244__overap_32_, v___y_30_);
v___x_245__overap_34_ = lp_mathlib_LinearMap_smulRight___redArg___lam__0(v___x_26_, v___x_27_, v___x_28_, v___y_29_);
v___x_35_ = lean_apply_1(v___x_245__overap_34_, v___y_30_);
v___x_36_ = lean_apply_2(v_toAddSemigroup_31_, v___x_33_, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extL___redArg(lean_object* v_inst_37_, lean_object* v_n_38_, lean_object* v_g_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_toSemiring_42_; lean_object* v_toAddCommMonoid_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___f_51_; 
v___x_40_ = lp_mathlib_Field_toSemifield___redArg(v_inst_37_);
v___x_41_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_40_);
v_toSemiring_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_toSemiring_42_);
lean_dec_ref(v___x_41_);
v_toAddCommMonoid_43_ = lean_ctor_get(v_toSemiring_42_, 0);
lean_inc_ref(v_toAddCommMonoid_43_);
v___x_44_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_42_);
lean_dec_ref(v_toSemiring_42_);
v___x_45_ = lp_mathlib_Pi_Function_module___redArg(v___x_44_);
lean_inc_n(v_n_38_, 3);
v___x_46_ = lp_tree_Formalism_L2_Col_incl___redArg(v_inst_37_, v_n_38_);
v___x_47_ = lp_tree_Formalism_L2_Col_initL___redArg(v_n_38_);
v___f_48_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_48_, 0, v___x_47_);
lean_closure_set(v___f_48_, 1, v_g_39_);
v___x_49_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_49_, 0, lean_box(0));
lean_closure_set(v___x_49_, 1, lean_box(0));
lean_closure_set(v___x_49_, 2, v_n_38_);
v___x_50_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_eLast), 4, 3);
lean_closure_set(v___x_50_, 0, lean_box(0));
lean_closure_set(v___x_50_, 1, v_inst_37_);
lean_closure_set(v___x_50_, 2, v_n_38_);
v___f_51_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extL___redArg___lam__0), 8, 6);
lean_closure_set(v___f_51_, 0, v_toAddCommMonoid_43_);
lean_closure_set(v___f_51_, 1, v___f_48_);
lean_closure_set(v___f_51_, 2, v___x_46_);
lean_closure_set(v___f_51_, 3, v___x_49_);
lean_closure_set(v___f_51_, 4, v___x_45_);
lean_closure_set(v___f_51_, 5, v___x_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extL(lean_object* v_E_52_, lean_object* v_inst_53_, lean_object* v_n_54_, lean_object* v_g_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_tree_Formalism_L2_Col_extL___redArg(v_inst_53_, v_n_54_, v_g_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extE___redArg(lean_object* v_inst_57_, lean_object* v_n_58_, lean_object* v_g_59_){
_start:
{
lean_object* v_toLinearMap_60_; lean_object* v___x_61_; lean_object* v_toLinearMap_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_toLinearMap_60_ = lean_ctor_get(v_g_59_, 0);
lean_inc(v_toLinearMap_60_);
v___x_61_ = lp_mathlib_LinearEquiv_symm___redArg(v_g_59_);
v_toLinearMap_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_toLinearMap_62_);
lean_dec_ref(v___x_61_);
lean_inc(v_n_58_);
lean_inc_ref(v_inst_57_);
v___x_63_ = lp_tree_Formalism_L2_Col_extL___redArg(v_inst_57_, v_n_58_, v_toLinearMap_60_);
v___x_64_ = lp_tree_Formalism_L2_Col_extL___redArg(v_inst_57_, v_n_58_, v_toLinearMap_62_);
v___x_65_ = lp_mathlib_LinearEquiv_ofLinearMap___redArg(v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extE(lean_object* v_E_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_g_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_tree_Formalism_L2_Col_extE___redArg(v_inst_67_, v_n_70_, v_g_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extE___boxed(lean_object* v_E_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_n_77_, lean_object* v_g_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Formalism_L2_Col_extE(v_E_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_n_77_, v_g_78_);
lean_dec(v_inst_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU___redArg___lam__0(lean_object* v_inst_80_, lean_object* v_n_81_, lean_object* v_g_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_tree_Formalism_L2_Col_extE___redArg(v_inst_80_, v_n_81_, v_g_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU___redArg(lean_object* v_inst_84_, lean_object* v_n_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extU___redArg___lam__0), 3, 2);
lean_closure_set(v___f_86_, 0, v_inst_84_);
lean_closure_set(v___f_86_, 1, v_n_85_);
return v___f_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU(lean_object* v_E_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_n_91_){
_start:
{
lean_object* v___f_92_; 
v___f_92_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extU___redArg___lam__0), 3, 2);
lean_closure_set(v___f_92_, 0, v_inst_88_);
lean_closure_set(v___f_92_, 1, v_n_91_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extU___boxed(lean_object* v_E_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_n_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_L2_Col_extU(v_E_93_, v_inst_94_, v_inst_95_, v_inst_96_, v_n_97_);
lean_dec(v_inst_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__0(lean_object* v_toZero_99_, lean_object* v_x_100_){
_start:
{
lean_inc(v_toZero_99_);
return v_toZero_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__0___boxed(lean_object* v_toZero_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_L2_Col_padM___redArg___lam__0(v_toZero_101_, v_x_102_);
lean_dec(v_x_102_);
lean_dec(v_toZero_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__1(lean_object* v_A_104_, lean_object* v_i_x27_105_, lean_object* v_j_x27_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_2(v_A_104_, v_i_x27_105_, v_j_x27_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__2(lean_object* v_A_108_, lean_object* v_n_109_, lean_object* v_toZero_110_, lean_object* v_j_111_, lean_object* v_i_x27_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; 
v___f_113_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_padM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_113_, 0, v_A_108_);
lean_closure_set(v___f_113_, 1, v_i_x27_112_);
v___x_114_ = l_Fin_lastCases___redArg(v_n_109_, v_toZero_110_, v___f_113_, v_j_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__2___boxed(lean_object* v_A_115_, lean_object* v_n_116_, lean_object* v_toZero_117_, lean_object* v_j_118_, lean_object* v_i_x27_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_tree_Formalism_L2_Col_padM___redArg___lam__2(v_A_115_, v_n_116_, v_toZero_117_, v_j_118_, v_i_x27_119_);
lean_dec(v_j_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__3(lean_object* v_A_121_, lean_object* v_n_122_, lean_object* v_toZero_123_, lean_object* v_toOne_124_, lean_object* v___f_125_, lean_object* v_i_126_, lean_object* v_j_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_inc(v_j_127_);
lean_inc_n(v_n_122_, 2);
v___f_128_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_padM___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_128_, 0, v_A_121_);
lean_closure_set(v___f_128_, 1, v_n_122_);
lean_closure_set(v___f_128_, 2, v_toZero_123_);
lean_closure_set(v___f_128_, 3, v_j_127_);
v___x_129_ = l_Fin_lastCases___redArg(v_n_122_, v_toOne_124_, v___f_125_, v_j_127_);
lean_dec(v_j_127_);
v___x_130_ = l_Fin_lastCases___redArg(v_n_122_, v___x_129_, v___f_128_, v_i_126_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__3___boxed(lean_object* v_A_131_, lean_object* v_n_132_, lean_object* v_toZero_133_, lean_object* v_toOne_134_, lean_object* v___f_135_, lean_object* v_i_136_, lean_object* v_j_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_tree_Formalism_L2_Col_padM___redArg___lam__3(v_A_131_, v_n_132_, v_toZero_133_, v_toOne_134_, v___f_135_, v_i_136_, v_j_137_);
lean_dec(v_i_136_);
return v_res_138_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_padM___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg___lam__4(lean_object* v_n_140_, lean_object* v_toZero_141_, lean_object* v_toOne_142_, lean_object* v___f_143_, lean_object* v_A_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_147_; lean_object* v_toFun_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&lp_tree_Formalism_L2_Col_padM___redArg___lam__4___closed__0, &lp_tree_Formalism_L2_Col_padM___redArg___lam__4___closed__0_once, _init_lp_tree_Formalism_L2_Col_padM___redArg___lam__4___closed__0);
v_toFun_148_ = lean_ctor_get(v___x_147_, 0);
v___f_149_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_padM___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_149_, 0, v_A_144_);
lean_closure_set(v___f_149_, 1, v_n_140_);
lean_closure_set(v___f_149_, 2, v_toZero_141_);
lean_closure_set(v___f_149_, 3, v_toOne_142_);
lean_closure_set(v___f_149_, 4, v___f_143_);
lean_inc(v_toFun_148_);
v___x_150_ = lean_apply_3(v_toFun_148_, v___f_149_, v___y_145_, v___y_146_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM___redArg(lean_object* v_inst_151_, lean_object* v_n_152_){
_start:
{
lean_object* v_toSemiring_153_; lean_object* v___x_154_; lean_object* v_toAddMonoidWithOne_155_; lean_object* v_toOne_156_; lean_object* v___x_157_; lean_object* v_toZero_158_; lean_object* v___f_159_; lean_object* v___f_160_; 
v_toSemiring_153_ = lean_ctor_get(v_inst_151_, 0);
lean_inc_ref(v_toSemiring_153_);
v___x_154_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_151_);
v_toAddMonoidWithOne_155_ = lean_ctor_get(v___x_154_, 1);
lean_inc_ref(v_toAddMonoidWithOne_155_);
lean_dec_ref(v___x_154_);
v_toOne_156_ = lean_ctor_get(v_toAddMonoidWithOne_155_, 2);
lean_inc(v_toOne_156_);
lean_dec_ref(v_toAddMonoidWithOne_155_);
v___x_157_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_153_);
v_toZero_158_ = lean_ctor_get(v___x_157_, 1);
lean_inc_n(v_toZero_158_, 2);
lean_dec_ref(v___x_157_);
v___f_159_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_padM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_159_, 0, v_toZero_158_);
v___f_160_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_padM___redArg___lam__4), 7, 4);
lean_closure_set(v___f_160_, 0, v_n_152_);
lean_closure_set(v___f_160_, 1, v_toZero_158_);
lean_closure_set(v___f_160_, 2, v_toOne_156_);
lean_closure_set(v___f_160_, 3, v___f_159_);
return v___f_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_padM(lean_object* v_R_161_, lean_object* v_inst_162_, lean_object* v_n_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lp_tree_Formalism_L2_Col_padM___redArg(v_inst_162_, v_n_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG___redArg___lam__0(lean_object* v___x_165_, lean_object* v_n_166_, lean_object* v_w_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; 
v___x_169_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_165_, v_w_167_);
v___x_170_ = lp_tree_Formalism_L2_Col_padM___redArg(v___x_169_, v_n_166_);
v___f_171_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_171_, 0, v___x_170_);
v___f_172_ = lean_alloc_closure((void*)(lp_mathlib_Pi_evalMulHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_172_, 0, v_w_167_);
v___x_173_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_172_, v___f_171_, v___y_168_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG___redArg(lean_object* v_inst_174_, lean_object* v_n_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___f_178_; 
v___x_176_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_174_);
v___f_177_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extG___redArg___lam__0), 4, 2);
lean_closure_set(v___f_177_, 0, v___x_176_);
lean_closure_set(v___f_177_, 1, v_n_175_);
v___f_178_ = lean_alloc_closure((void*)(lp_mathlib_MulHom_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_178_, 0, v___f_177_);
return v___f_178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG(lean_object* v_E_179_, lean_object* v_inst_180_, lean_object* v_n_181_, lean_object* v_SG_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lp_tree_Formalism_L2_Col_extG___redArg(v_inst_180_, v_n_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extG___boxed(lean_object* v_E_184_, lean_object* v_inst_185_, lean_object* v_n_186_, lean_object* v_SG_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_tree_Formalism_L2_Col_extG(v_E_184_, v_inst_185_, v_n_186_, v_SG_187_);
lean_dec(v_SG_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin___redArg___lam__0(lean_object* v_d_189_, lean_object* v_P_190_, lean_object* v_y_191_){
_start:
{
lean_object* v_f_192_; lean_object* v___x_193_; 
v_f_192_ = lean_ctor_get(v_d_189_, 1);
lean_inc(v_f_192_);
lean_dec_ref(v_d_189_);
v___x_193_ = lean_apply_2(v_f_192_, v_P_190_, v_y_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin___redArg(lean_object* v_d_194_, lean_object* v_P_195_){
_start:
{
lean_object* v___f_196_; 
v___f_196_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Deco_Ok_fLin___redArg___lam__0), 3, 2);
lean_closure_set(v___f_196_, 0, v_d_194_);
lean_closure_set(v___f_196_, 1, v_P_195_);
return v___f_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin(lean_object* v_E_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_n_201_, lean_object* v_ST_202_, lean_object* v_SG_203_, lean_object* v_d_204_, lean_object* v_hd_205_, lean_object* v_P_206_, lean_object* v_M_207_, lean_object* v_hM_208_){
_start:
{
lean_object* v___f_209_; 
v___f_209_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Deco_Ok_fLin___redArg___lam__0), 3, 2);
lean_closure_set(v___f_209_, 0, v_d_204_);
lean_closure_set(v___f_209_, 1, v_P_206_);
return v___f_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_Ok_fLin___boxed(lean_object* v_E_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_n_214_, lean_object* v_ST_215_, lean_object* v_SG_216_, lean_object* v_d_217_, lean_object* v_hd_218_, lean_object* v_P_219_, lean_object* v_M_220_, lean_object* v_hM_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = lp_tree_Formalism_L2_Col_Deco_Ok_fLin(v_E_210_, v_inst_211_, v_inst_212_, v_inst_213_, v_n_214_, v_ST_215_, v_SG_216_, v_d_217_, v_hd_218_, v_P_219_, v_M_220_, v_hM_221_);
lean_dec(v_SG_216_);
lean_dec(v_ST_215_);
lean_dec(v_n_214_);
lean_dec(v_inst_213_);
lean_dec_ref(v_inst_211_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___lam__0(lean_object* v_P_223_, lean_object* v___y_224_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___lam__0___boxed(lean_object* v_P_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___lam__0(v_P_225_, v___y_226_);
lean_dec(v___y_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg(lean_object* v_d_229_){
_start:
{
lean_object* v_N_230_; lean_object* v_be_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_N_230_ = lean_ctor_get(v_d_229_, 0);
v_be_231_ = lean_ctor_get(v_d_229_, 2);
v_isSharedCheck_239_ = !lean_is_exclusive(v_d_229_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v_d_229_, 1);
lean_dec(v_unused_240_);
v___x_233_ = v_d_229_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_be_231_);
lean_inc(v_N_230_);
lean_dec(v_d_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___f_235_; lean_object* v___x_237_; 
v___f_235_ = ((lean_object*)(lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg___closed__0));
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___f_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_N_230_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___f_235_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_be_231_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT(lean_object* v_E_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_n_244_, lean_object* v_ST_245_, lean_object* v_SG_246_, lean_object* v_d_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lp_tree_Formalism_L2_Col_DecoSet_forgetT___redArg(v_d_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_forgetT___boxed(lean_object* v_E_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_n_252_, lean_object* v_ST_253_, lean_object* v_SG_254_, lean_object* v_d_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = lp_tree_Formalism_L2_Col_DecoSet_forgetT(v_E_249_, v_inst_250_, v_inst_251_, v_n_252_, v_ST_253_, v_SG_254_, v_d_255_);
lean_dec(v_SG_254_);
lean_dec(v_ST_253_);
lean_dec(v_n_252_);
lean_dec(v_inst_251_);
lean_dec_ref(v_inst_250_);
return v_res_256_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_BaseLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_FinalNeighbourConstruct(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_KpqSubgroupCompact(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_DecoFin(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_BaseLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_FinalNeighbourConstruct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_KpqSubgroupCompact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
