// Lean compiler output
// Module: Formalism.LocalToGlobal.KernelLattices.ThDistC
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_Wts_nuW___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_tree_Formalism_L2_Col_Fields_embC(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Ker_Seam_lat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Ker_Seam_lat_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast___redArg(lean_object* v_R_1_, lean_object* v_W_2_, lean_object* v_u_3_, lean_object* v_i_4_, lean_object* v_00_u03c4_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_add(v_i_4_, v___x_6_);
v___x_8_ = lean_nat_sub(v___x_7_, v___x_6_);
v___x_9_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_1_, v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lp_tree_Formalism_L2_Col_Wts_nuW___redArg(v_R_1_, v_W_2_, v_u_3_, v___x_7_, v_00_u03c4_5_);
v___x_11_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v___x_9_, v___x_10_);
lean_dec(v___x_9_);
v___x_12_ = l_Int_toNat(v___x_11_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast___redArg___boxed(lean_object* v_R_13_, lean_object* v_W_14_, lean_object* v_u_15_, lean_object* v_i_16_, lean_object* v_00_u03c4_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Ker_nuLast___redArg(v_R_13_, v_W_14_, v_u_15_, v_i_16_, v_00_u03c4_17_);
lean_dec(v_i_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast(lean_object* v_X_19_, lean_object* v_Pr_20_, lean_object* v_R_21_, lean_object* v_W_22_, lean_object* v_u_23_, lean_object* v_i_24_, lean_object* v_00_u03c4_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_Formalism_L2_Ker_nuLast___redArg(v_R_21_, v_W_22_, v_u_23_, v_i_24_, v_00_u03c4_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_nuLast___boxed(lean_object* v_X_27_, lean_object* v_Pr_28_, lean_object* v_R_29_, lean_object* v_W_30_, lean_object* v_u_31_, lean_object* v_i_32_, lean_object* v_00_u03c4_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_L2_Ker_nuLast(v_X_27_, v_Pr_28_, v_R_29_, v_W_30_, v_u_31_, v_i_32_, v_00_u03c4_33_);
lean_dec(v_i_32_);
lean_dec_ref(v_Pr_28_);
lean_dec_ref(v_X_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___lam__0(lean_object* v_toZero_35_, lean_object* v_x_36_){
_start:
{
lean_inc(v_toZero_35_);
return v_toZero_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___lam__0___boxed(lean_object* v_toZero_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___lam__0(v_toZero_37_, v_x_38_);
lean_dec(v_x_38_);
lean_dec(v_toZero_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg(lean_object* v_X_40_, lean_object* v_i_41_, lean_object* v_x_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_fieldE_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toSemiring_47_; lean_object* v___x_48_; lean_object* v_toZero_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
v_fieldE_44_ = lean_ctor_get(v_X_40_, 1);
v___x_45_ = lp_mathlib_Field_toSemifield___redArg(v_fieldE_44_);
v___x_46_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_45_);
v_toSemiring_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_toSemiring_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_47_);
v_toZero_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_toZero_49_);
lean_dec_ref(v___x_48_);
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_50_, 0, v_toZero_49_);
v___x_51_ = lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(v___f_50_, v_i_41_, v_x_42_, v_a_43_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg___boxed(lean_object* v_X_52_, lean_object* v_i_53_, lean_object* v_x_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg(v_X_52_, v_i_53_, v_x_54_, v_a_55_);
lean_dec(v_x_54_);
lean_dec(v_i_53_);
lean_dec_ref(v_X_52_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__0(lean_object* v_X_57_, lean_object* v_j_58_, lean_object* v_toOne_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg(v_X_57_, v_j_58_, v_toOne_59_, v___y_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__0___boxed(lean_object* v_X_62_, lean_object* v_j_63_, lean_object* v_toOne_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_L2_Ker_Amb_pullV___lam__0(v_X_62_, v_j_63_, v_toOne_64_, v___y_65_);
lean_dec(v_toOne_64_);
lean_dec(v_j_63_);
lean_dec_ref(v_X_62_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__1(lean_object* v_X_67_, lean_object* v_k_68_, lean_object* v_toOne_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg(v_X_67_, v_k_68_, v_toOne_69_, v___y_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__1___boxed(lean_object* v_X_72_, lean_object* v_k_73_, lean_object* v_toOne_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_L2_Ker_Amb_pullV___lam__1(v_X_72_, v_k_73_, v_toOne_74_, v___y_75_);
lean_dec(v_toOne_74_);
lean_dec(v_k_73_);
lean_dec_ref(v_X_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg___lam__0(lean_object* v_invFun_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_apply_2(v_invFun_77_, v___y_78_, v___y_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___redArg(lean_object* v_self_81_){
_start:
{
lean_object* v_toLinearMap_82_; lean_object* v_invFun_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_toLinearMap_82_ = lean_ctor_get(v_self_81_, 0);
v_invFun_83_ = lean_ctor_get(v_self_81_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_self_81_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v_self_81_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_invFun_83_);
lean_inc(v_toLinearMap_82_);
lean_dec(v_self_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_toLinearMap_82_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_invFun_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg(lean_object* v_X_91_, lean_object* v_00_u03c3_92_, lean_object* v_00_u03c3_x27_93_, lean_object* v_e_94_){
_start:
{
lean_object* v_invFun_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_invFun_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_invFun_95_ = lean_ctor_get(v_e_94_, 1);
lean_inc(v_invFun_95_);
v___x_96_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___redArg(v_e_94_);
v___x_97_ = lp_mathlib_Equiv_symm___redArg(v___x_96_);
v_invFun_98_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_97_, 0);
lean_dec(v_unused_107_);
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_invFun_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___f_102_; lean_object* v___x_104_; 
v___f_102_ = lean_alloc_closure((void*)(lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_102_, 0, v_invFun_95_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___f_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___f_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_invFun_98_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg___boxed(lean_object* v_X_108_, lean_object* v_00_u03c3_109_, lean_object* v_00_u03c3_x27_110_, lean_object* v_e_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg(v_X_108_, v_00_u03c3_109_, v_00_u03c3_x27_110_, v_e_111_);
lean_dec(v_00_u03c3_x27_110_);
lean_dec(v_00_u03c3_109_);
lean_dec_ref(v_X_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2(lean_object* v_A_114_, lean_object* v_X_115_, lean_object* v_00_u03b3_x27_116_, lean_object* v___f_117_, lean_object* v_i_118_, lean_object* v_00_u03c4_119_, lean_object* v_00_u03b3_120_, lean_object* v_z_121_, lean_object* v_k_122_, lean_object* v___f_123_, lean_object* v_l_124_){
_start:
{
lean_object* v_00_u03c3_u2080_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v_toLinearMap_128_; lean_object* v___x_129_; lean_object* v___x_779__overap_130_; lean_object* v___x_131_; lean_object* v_re_132_; lean_object* v_im_133_; lean_object* v_toLinearMap_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_re_137_; lean_object* v_im_138_; lean_object* v___x_139_; lean_object* v___x_783__overap_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_00_u03c3_u2080_125_ = lean_ctor_get(v_A_114_, 0);
lean_inc_ref_n(v_00_u03c3_u2080_125_, 2);
lean_dec_ref(v_A_114_);
v___f_126_ = ((lean_object*)(lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2___closed__0));
v___x_127_ = lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg(v_X_115_, v___f_126_, v___f_126_, v_00_u03b3_x27_116_);
v_toLinearMap_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_toLinearMap_128_);
lean_dec_ref(v___x_127_);
v___x_129_ = lean_apply_2(v_toLinearMap_128_, v___f_117_, v_i_118_);
lean_inc_n(v_00_u03c4_119_, 2);
lean_inc_ref(v_X_115_);
v___x_779__overap_130_ = lp_tree_Formalism_L2_Col_Fields_embC(v_X_115_, v_00_u03c3_u2080_125_, v_00_u03c4_119_);
v___x_131_ = lean_apply_1(v___x_779__overap_130_, v___x_129_);
v_re_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_re_132_);
v_im_133_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_im_133_);
lean_dec_ref(v___x_131_);
v_toLinearMap_134_ = lean_ctor_get(v_00_u03b3_120_, 0);
lean_inc(v_toLinearMap_134_);
lean_dec_ref(v_00_u03b3_120_);
lean_inc(v_l_124_);
v___x_135_ = lean_apply_3(v_z_121_, v_00_u03c4_119_, v_k_122_, v_l_124_);
v___x_136_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_132_, v_im_133_, v___x_135_);
v_re_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_re_137_);
v_im_138_ = lean_ctor_get(v___x_136_, 1);
lean_inc(v_im_138_);
lean_dec_ref(v___x_136_);
v___x_139_ = lean_apply_2(v_toLinearMap_134_, v___f_123_, v_l_124_);
v___x_783__overap_140_ = lp_tree_Formalism_L2_Col_Fields_embC(v_X_115_, v_00_u03c3_u2080_125_, v_00_u03c4_119_);
v___x_141_ = lean_apply_1(v___x_783__overap_140_, v___x_139_);
v___x_142_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_137_, v_im_138_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV___lam__3(lean_object* v_X_143_, lean_object* v_toOne_144_, lean_object* v_A_145_, lean_object* v_00_u03b3_x27_146_, lean_object* v_i_147_, lean_object* v_00_u03c4_148_, lean_object* v_00_u03b3_149_, lean_object* v_z_150_, lean_object* v___f_151_, lean_object* v_a_152_, lean_object* v_k_153_){
_start:
{
lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_inc(v_k_153_);
lean_inc_ref(v_X_143_);
v___f_154_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_Amb_pullV___lam__1___boxed), 4, 3);
lean_closure_set(v___f_154_, 0, v_X_143_);
lean_closure_set(v___f_154_, 1, v_k_153_);
lean_closure_set(v___f_154_, 2, v_toOne_144_);
v___f_155_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_Amb_pullV___lam__2), 11, 10);
lean_closure_set(v___f_155_, 0, v_A_145_);
lean_closure_set(v___f_155_, 1, v_X_143_);
lean_closure_set(v___f_155_, 2, v_00_u03b3_x27_146_);
lean_closure_set(v___f_155_, 3, v___f_154_);
lean_closure_set(v___f_155_, 4, v_i_147_);
lean_closure_set(v___f_155_, 5, v_00_u03c4_148_);
lean_closure_set(v___f_155_, 6, v_00_u03b3_149_);
lean_closure_set(v___f_155_, 7, v_z_150_);
lean_closure_set(v___f_155_, 8, v_k_153_);
lean_closure_set(v___f_155_, 9, v___f_151_);
v___x_156_ = l_List_finRange(v_a_152_);
v___x_157_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v___x_156_, v___f_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Amb_pullV(lean_object* v_X_158_, lean_object* v_A_159_, lean_object* v_a_160_, lean_object* v_b_161_, lean_object* v_00_u03b3_162_, lean_object* v_00_u03b3_x27_163_, lean_object* v_z_164_, lean_object* v_00_u03c4_165_, lean_object* v_i_166_, lean_object* v_j_167_){
_start:
{
lean_object* v_fieldE_168_; lean_object* v___x_169_; lean_object* v_toRing_170_; lean_object* v___x_171_; lean_object* v_toAddMonoidWithOne_172_; lean_object* v_toOne_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v_fieldE_168_ = lean_ctor_get(v_X_158_, 1);
lean_inc_ref(v_fieldE_168_);
v___x_169_ = lp_mathlib_Field_toDivisionRing___redArg(v_fieldE_168_);
v_toRing_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_toRing_170_);
lean_dec_ref(v___x_169_);
v___x_171_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_170_);
v_toAddMonoidWithOne_172_ = lean_ctor_get(v___x_171_, 1);
lean_inc_ref(v_toAddMonoidWithOne_172_);
lean_dec_ref(v___x_171_);
v_toOne_173_ = lean_ctor_get(v_toAddMonoidWithOne_172_, 2);
lean_inc_n(v_toOne_173_, 2);
lean_dec_ref(v_toAddMonoidWithOne_172_);
v___x_174_ = l_List_finRange(v_b_161_);
lean_inc_ref(v_X_158_);
v___f_175_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_Amb_pullV___lam__0___boxed), 4, 3);
lean_closure_set(v___f_175_, 0, v_X_158_);
lean_closure_set(v___f_175_, 1, v_j_167_);
lean_closure_set(v___f_175_, 2, v_toOne_173_);
v___f_176_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_Amb_pullV___lam__3), 11, 10);
lean_closure_set(v___f_176_, 0, v_X_158_);
lean_closure_set(v___f_176_, 1, v_toOne_173_);
lean_closure_set(v___f_176_, 2, v_A_159_);
lean_closure_set(v___f_176_, 3, v_00_u03b3_x27_163_);
lean_closure_set(v___f_176_, 4, v_i_166_);
lean_closure_set(v___f_176_, 5, v_00_u03c4_165_);
lean_closure_set(v___f_176_, 6, v_00_u03b3_162_);
lean_closure_set(v___f_176_, 7, v_z_164_);
lean_closure_set(v___f_176_, 8, v___f_175_);
lean_closure_set(v___f_176_, 9, v_a_160_);
v___x_177_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v___x_174_, v___f_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___redArg(lean_object* v_g_178_){
_start:
{
lean_inc(v_g_178_);
return v_g_178_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___redArg___boxed(lean_object* v_g_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___redArg(v_g_179_);
lean_dec(v_g_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0(lean_object* v_X_181_, lean_object* v_00_u03c3_182_, lean_object* v_00_u03c3_x27_183_, lean_object* v_inst_184_, lean_object* v_f_185_, lean_object* v_g_186_, lean_object* v_h_u2081_187_, lean_object* v_h_u2082_188_){
_start:
{
lean_inc(v_g_186_);
return v_g_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0___boxed(lean_object* v_X_189_, lean_object* v_00_u03c3_190_, lean_object* v_00_u03c3_x27_191_, lean_object* v_inst_192_, lean_object* v_f_193_, lean_object* v_g_194_, lean_object* v_h_u2081_195_, lean_object* v_h_u2082_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__0(v_X_189_, v_00_u03c3_190_, v_00_u03c3_x27_191_, v_inst_192_, v_f_193_, v_g_194_, v_h_u2081_195_, v_h_u2082_196_);
lean_dec(v_g_194_);
lean_dec(v_f_193_);
lean_dec(v_00_u03c3_x27_191_);
lean_dec(v_00_u03c3_190_);
lean_dec_ref(v_X_189_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0(lean_object* v_X_198_, lean_object* v_00_u03c3_199_, lean_object* v_00_u03c3_x27_200_, lean_object* v_re_u2081_201_, lean_object* v_re_u2082_202_, lean_object* v_e_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___redArg(v_X_198_, v_00_u03c3_199_, v_00_u03c3_x27_200_, v_e_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0___boxed(lean_object* v_X_205_, lean_object* v_00_u03c3_206_, lean_object* v_00_u03c3_x27_207_, lean_object* v_re_u2081_208_, lean_object* v_re_u2082_209_, lean_object* v_e_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0(v_X_205_, v_00_u03c3_206_, v_00_u03c3_x27_207_, v_re_u2081_208_, v_re_u2082_209_, v_e_210_);
lean_dec(v_00_u03c3_x27_207_);
lean_dec(v_00_u03c3_206_);
lean_dec_ref(v_X_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1(lean_object* v_X_212_, lean_object* v_b_213_, lean_object* v_i_214_, lean_object* v_x_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___redArg(v_X_212_, v_i_214_, v_x_215_, v_a_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1___boxed(lean_object* v_X_218_, lean_object* v_b_219_, lean_object* v_i_220_, lean_object* v_x_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_tree_Pi_single___at___00Formalism_L2_Ker_Amb_pullV_spec__1(v_X_218_, v_b_219_, v_i_220_, v_x_221_, v_a_222_);
lean_dec(v_x_221_);
lean_dec(v_i_220_);
lean_dec(v_b_219_);
lean_dec_ref(v_X_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2(lean_object* v_X_224_, lean_object* v_00_u03c3_225_, lean_object* v_00_u03c3_x27_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_self_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___redArg(v_self_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___boxed(lean_object* v_X_231_, lean_object* v_00_u03c3_232_, lean_object* v_00_u03c3_x27_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_self_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2(v_X_231_, v_00_u03c3_232_, v_00_u03c3_x27_233_, v_inst_234_, v_inst_235_, v_self_236_);
lean_dec(v_00_u03c3_x27_233_);
lean_dec(v_00_u03c3_232_);
lean_dec_ref(v_X_231_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___redArg(lean_object* v_X_238_, lean_object* v_00_u03c3_239_, lean_object* v_00_u03c3_x27_240_, lean_object* v_e_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___redArg(v_e_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___redArg___boxed(lean_object* v_X_243_, lean_object* v_00_u03c3_244_, lean_object* v_00_u03c3_x27_245_, lean_object* v_e_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___redArg(v_X_243_, v_00_u03c3_244_, v_00_u03c3_x27_245_, v_e_246_);
lean_dec(v_00_u03c3_x27_245_);
lean_dec(v_00_u03c3_244_);
lean_dec_ref(v_X_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1(lean_object* v_X_248_, lean_object* v_00_u03c3_249_, lean_object* v_00_u03c3_x27_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_e_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1_spec__2___redArg(v_e_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1___boxed(lean_object* v_X_255_, lean_object* v_00_u03c3_256_, lean_object* v_00_u03c3_x27_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_e_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Formalism_L2_Ker_Amb_pullV_spec__0_spec__1(v_X_255_, v_00_u03c3_256_, v_00_u03c3_x27_257_, v_inst_258_, v_inst_259_, v_e_260_);
lean_dec(v_00_u03c3_x27_257_);
lean_dec(v_00_u03c3_256_);
lean_dec_ref(v_X_255_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___redArg___lam__0(lean_object* v_toAddMonoid_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_266_; lean_object* v_toZero_267_; 
v___x_266_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_262_);
v_toZero_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_toZero_267_);
lean_dec_ref(v___x_266_);
return v_toZero_267_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___redArg___lam__0___boxed(lean_object* v_toAddMonoid_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = lp_tree_Formalism_L2_Ker_zeroKer___redArg___lam__0(v_toAddMonoid_268_, v_x_269_, v_x_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec(v_x_270_);
lean_dec(v_x_269_);
lean_dec_ref(v_toAddMonoid_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___redArg(lean_object* v_S_x27_273_){
_start:
{
lean_object* v_addV_274_; lean_object* v_toAddMonoid_275_; lean_object* v___f_276_; 
v_addV_274_ = lean_ctor_get(v_S_x27_273_, 2);
lean_inc_ref(v_addV_274_);
lean_dec_ref(v_S_x27_273_);
v_toAddMonoid_275_ = lean_ctor_get(v_addV_274_, 0);
lean_inc_ref(v_toAddMonoid_275_);
lean_dec_ref(v_addV_274_);
v___f_276_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_zeroKer___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_276_, 0, v_toAddMonoid_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer(lean_object* v_K_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_S_281_, lean_object* v_S_x27_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lp_tree_Formalism_L2_Ker_zeroKer___redArg(v_S_x27_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_zeroKer___boxed(lean_object* v_K_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_S_288_, lean_object* v_S_x27_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = lp_tree_Formalism_L2_Ker_zeroKer(v_K_284_, v_inst_285_, v_inst_286_, v_inst_287_, v_S_288_, v_S_x27_289_);
lean_dec_ref(v_S_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Ker_Seam_lat_spec__0(lean_object* v___x_291_, lean_object* v_s_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Ker_Seam_lat_spec__0___boxed(lean_object* v___x_294_, lean_object* v_s_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = lp_tree_Submodule_span___at___00Formalism_L2_Ker_Seam_lat_spec__0(v___x_294_, v_s_295_);
lean_dec_ref(v___x_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat___redArg(lean_object* v_D_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_box(0);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat___redArg___boxed(lean_object* v_D_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = lp_tree_Formalism_L2_Ker_Seam_lat___redArg(v_D_299_);
lean_dec_ref(v_D_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat(lean_object* v_D_301_, lean_object* v_X_302_, lean_object* v_s_303_, lean_object* v_n_304_, lean_object* v_N_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_box(0);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Seam_lat___boxed(lean_object* v_D_307_, lean_object* v_X_308_, lean_object* v_s_309_, lean_object* v_n_310_, lean_object* v_N_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = lp_tree_Formalism_L2_Ker_Seam_lat(v_D_307_, v_X_308_, v_s_309_, v_n_310_, v_N_311_);
lean_dec(v_n_310_);
lean_dec_ref(v_s_309_);
lean_dec_ref(v_X_308_);
lean_dec_ref(v_D_307_);
return v_res_312_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_KernelLattices_XiIndCClass(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_KernelLattices_LateralTheory(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_KernelLattices_ThDistC(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_KernelLattices_XiIndCClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_KernelLattices_LateralTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
