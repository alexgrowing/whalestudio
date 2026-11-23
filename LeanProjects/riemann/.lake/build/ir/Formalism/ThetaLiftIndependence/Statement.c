// Lean compiler output
// Module: Formalism.ThetaLiftIndependence.Statement
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.StatementLat public import Formalism.HermitianLattices.StatementTheta public import Formalism.SatakeDualWeyl.Statement
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_unitsEquivProdSubtype(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_pmap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerMul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_wip___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_wip___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_wip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerAdj___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerAdj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerAdj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__3(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg___lam__0(lean_object* v_w_1_, lean_object* v_f_2_, lean_object* v_toMul_3_, lean_object* v_K_4_, lean_object* v_j_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
lean_inc_n(v_i_6_, 2);
v___x_7_ = lean_apply_1(v_w_1_, v_i_6_);
v___x_8_ = lean_apply_1(v_f_2_, v_i_6_);
lean_inc(v_toMul_3_);
v___x_9_ = lean_apply_2(v_toMul_3_, v___x_7_, v___x_8_);
v___x_10_ = lean_apply_2(v_K_4_, v_i_6_, v_j_5_);
v___x_11_ = lean_apply_2(v_toMul_3_, v___x_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_w_14_, lean_object* v_K_15_, lean_object* v_f_16_, lean_object* v_j_17_){
_start:
{
lean_object* v_toAddCommMonoid_18_; lean_object* v___x_19_; lean_object* v_toMul_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v_toAddCommMonoid_18_ = lean_ctor_get(v_inst_12_, 0);
lean_inc_ref(v_toAddCommMonoid_18_);
v___x_19_ = lp_mathlib_instDistribOfSemiring___redArg(v_inst_12_);
v_toMul_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_toMul_20_);
lean_dec_ref(v___x_19_);
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg___lam__0), 6, 5);
lean_closure_set(v___f_21_, 0, v_w_14_);
lean_closure_set(v___f_21_, 1, v_f_16_);
lean_closure_set(v___f_21_, 2, v_toMul_20_);
lean_closure_set(v___f_21_, 3, v_K_15_);
lean_closure_set(v___f_21_, 4, v_j_17_);
v___x_22_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_18_, v_inst_13_, v___f_21_);
lean_dec_ref(v_toAddCommMonoid_18_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOp(lean_object* v_R_23_, lean_object* v_00_u03b9_24_, lean_object* v_00_u03ba_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_w_28_, lean_object* v_K_29_, lean_object* v_f_30_, lean_object* v_j_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg(v_inst_26_, v_inst_27_, v_w_28_, v_K_29_, v_f_30_, v_j_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerMul___redArg___lam__0(lean_object* v_K_u2081_33_, lean_object* v_i_34_, lean_object* v_w_35_, lean_object* v_toMul_36_, lean_object* v_K_u2082_37_, lean_object* v_k_38_, lean_object* v_j_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc_n(v_j_39_, 2);
v___x_40_ = lean_apply_2(v_K_u2081_33_, v_i_34_, v_j_39_);
v___x_41_ = lean_apply_1(v_w_35_, v_j_39_);
lean_inc(v_toMul_36_);
v___x_42_ = lean_apply_2(v_toMul_36_, v___x_40_, v___x_41_);
v___x_43_ = lean_apply_2(v_K_u2082_37_, v_j_39_, v_k_38_);
v___x_44_ = lean_apply_2(v_toMul_36_, v___x_42_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerMul___redArg(lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_w_47_, lean_object* v_K_u2081_48_, lean_object* v_K_u2082_49_, lean_object* v_i_50_, lean_object* v_k_51_){
_start:
{
lean_object* v_toAddCommMonoid_52_; lean_object* v___x_53_; lean_object* v_toMul_54_; lean_object* v___f_55_; lean_object* v___x_56_; 
v_toAddCommMonoid_52_ = lean_ctor_get(v_inst_45_, 0);
lean_inc_ref(v_toAddCommMonoid_52_);
v___x_53_ = lp_mathlib_instDistribOfSemiring___redArg(v_inst_45_);
v_toMul_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_toMul_54_);
lean_dec_ref(v___x_53_);
v___f_55_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_kerMul___redArg___lam__0), 7, 6);
lean_closure_set(v___f_55_, 0, v_K_u2081_48_);
lean_closure_set(v___f_55_, 1, v_i_50_);
lean_closure_set(v___f_55_, 2, v_w_47_);
lean_closure_set(v___f_55_, 3, v_toMul_54_);
lean_closure_set(v___f_55_, 4, v_K_u2082_49_);
lean_closure_set(v___f_55_, 5, v_k_51_);
v___x_56_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_52_, v_inst_46_, v___f_55_);
lean_dec_ref(v_toAddCommMonoid_52_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerMul(lean_object* v_R_57_, lean_object* v_00_u03b9_58_, lean_object* v_00_u03ba_59_, lean_object* v_00_u03bc_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_w_63_, lean_object* v_K_u2081_64_, lean_object* v_K_u2082_65_, lean_object* v_i_66_, lean_object* v_k_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_tree_Formalism_ThetaLiftIndependence_kerMul___redArg(v_inst_61_, v_inst_62_, v_w_63_, v_K_u2081_64_, v_K_u2082_65_, v_i_66_, v_k_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_wip___redArg___lam__0(lean_object* v_w_69_, lean_object* v_f_70_, lean_object* v_inst_71_, lean_object* v_toMul_72_, lean_object* v_g_73_, lean_object* v_i_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
lean_inc_n(v_i_74_, 2);
v___x_75_ = lean_apply_1(v_w_69_, v_i_74_);
v___x_76_ = lean_apply_1(v_f_70_, v_i_74_);
v___x_77_ = lean_apply_1(v_inst_71_, v___x_76_);
lean_inc(v_toMul_72_);
v___x_78_ = lean_apply_2(v_toMul_72_, v___x_75_, v___x_77_);
v___x_79_ = lean_apply_1(v_g_73_, v_i_74_);
v___x_80_ = lean_apply_2(v_toMul_72_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_wip___redArg(lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_w_84_, lean_object* v_f_85_, lean_object* v_g_86_){
_start:
{
lean_object* v_toAddCommMonoid_87_; lean_object* v___x_88_; lean_object* v_toMul_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
v_toAddCommMonoid_87_ = lean_ctor_get(v_inst_81_, 0);
lean_inc_ref(v_toAddCommMonoid_87_);
v___x_88_ = lp_mathlib_instDistribOfSemiring___redArg(v_inst_81_);
v_toMul_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_toMul_89_);
lean_dec_ref(v___x_88_);
v___f_90_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_wip___redArg___lam__0), 6, 5);
lean_closure_set(v___f_90_, 0, v_w_84_);
lean_closure_set(v___f_90_, 1, v_f_85_);
lean_closure_set(v___f_90_, 2, v_inst_82_);
lean_closure_set(v___f_90_, 3, v_toMul_89_);
lean_closure_set(v___f_90_, 4, v_g_86_);
v___x_91_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_87_, v_inst_83_, v___f_90_);
lean_dec_ref(v_toAddCommMonoid_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_wip(lean_object* v_R_92_, lean_object* v_00_u03b9_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_w_97_, lean_object* v_f_98_, lean_object* v_g_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_tree_Formalism_ThetaLiftIndependence_wip___redArg(v_inst_94_, v_inst_95_, v_inst_96_, v_w_97_, v_f_98_, v_g_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerAdj___redArg(lean_object* v_inst_101_, lean_object* v_K_102_, lean_object* v_j_103_, lean_object* v_i_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_apply_2(v_K_102_, v_i_104_, v_j_103_);
v___x_106_ = lean_apply_1(v_inst_101_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerAdj(lean_object* v_R_107_, lean_object* v_00_u03b9_108_, lean_object* v_00_u03ba_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_K_112_, lean_object* v_j_113_, lean_object* v_i_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_tree_Formalism_ThetaLiftIndependence_kerAdj___redArg(v_inst_111_, v_K_112_, v_j_113_, v_i_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerAdj___boxed(lean_object* v_R_116_, lean_object* v_00_u03b9_117_, lean_object* v_00_u03ba_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_K_121_, lean_object* v_j_122_, lean_object* v_i_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_Formalism_ThetaLiftIndependence_kerAdj(v_R_116_, v_00_u03b9_117_, v_00_u03ba_118_, v_inst_119_, v_inst_120_, v_K_121_, v_j_122_, v_i_123_);
lean_dec_ref(v_inst_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg___boxed(lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_w_127_, lean_object* v_K_128_, lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg(v_inst_125_, v_inst_126_, v_w_127_, v_K_128_, v_x_129_, v_x_130_, v_a_131_);
lean_dec(v_x_129_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg(lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_w_135_, lean_object* v_K_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_zero_140_; uint8_t v_isZero_141_; 
v_zero_140_ = lean_unsigned_to_nat(0u);
v_isZero_141_ = lean_nat_dec_eq(v_x_137_, v_zero_140_);
if (v_isZero_141_ == 1)
{
lean_object* v___x_142_; 
lean_dec(v_K_136_);
lean_dec(v_w_135_);
lean_dec(v_inst_134_);
lean_dec_ref(v_inst_133_);
v___x_142_ = lean_apply_1(v_x_138_, v_a_139_);
return v___x_142_;
}
else
{
lean_object* v_one_143_; lean_object* v_n_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_one_143_ = lean_unsigned_to_nat(1u);
v_n_144_ = lean_nat_sub(v_x_137_, v_one_143_);
lean_inc(v_inst_134_);
lean_inc_n(v_n_144_, 3);
v___x_145_ = lean_apply_1(v_inst_134_, v_n_144_);
lean_inc(v_w_135_);
v___x_146_ = lean_apply_1(v_w_135_, v_n_144_);
lean_inc(v_K_136_);
v___x_147_ = lean_apply_1(v_K_136_, v_n_144_);
lean_inc_ref(v_inst_133_);
v___x_148_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg___boxed), 7, 6);
lean_closure_set(v___x_148_, 0, v_inst_133_);
lean_closure_set(v___x_148_, 1, v_inst_134_);
lean_closure_set(v___x_148_, 2, v_w_135_);
lean_closure_set(v___x_148_, 3, v_K_136_);
lean_closure_set(v___x_148_, 4, v_n_144_);
lean_closure_set(v___x_148_, 5, v_x_138_);
v___x_149_ = lp_tree_Formalism_ThetaLiftIndependence_kerOp___redArg(v_inst_133_, v___x_145_, v___x_146_, v___x_147_, v___x_148_, v_a_139_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp(lean_object* v_R_150_, lean_object* v_inst_151_, lean_object* v_00_u03b9_152_, lean_object* v_inst_153_, lean_object* v_w_154_, lean_object* v_K_155_, lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lp_tree_Formalism_ThetaLiftIndependence_chainOp___redArg(v_inst_151_, v_inst_153_, v_w_154_, v_K_155_, v_x_156_, v_x_157_, v_a_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOp___boxed(lean_object* v_R_160_, lean_object* v_inst_161_, lean_object* v_00_u03b9_162_, lean_object* v_inst_163_, lean_object* v_w_164_, lean_object* v_K_165_, lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = lp_tree_Formalism_ThetaLiftIndependence_chainOp(v_R_160_, v_inst_161_, v_00_u03b9_162_, v_inst_163_, v_w_164_, v_K_165_, v_x_166_, v_x_167_, v_a_168_);
lean_dec(v_x_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg___lam__0(lean_object* v_w_170_, lean_object* v_f_171_, lean_object* v_K_172_, lean_object* v_j_173_, lean_object* v_inst_174_, lean_object* v_i_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_n(v_i_175_, 2);
v___x_176_ = lean_apply_1(v_w_170_, v_i_175_);
v___x_177_ = lean_apply_1(v_f_171_, v_i_175_);
v___x_178_ = lean_apply_3(v_K_172_, v_i_175_, v_j_173_, v___x_177_);
v___x_179_ = lean_apply_2(v_inst_174_, v___x_176_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_w_183_, lean_object* v_K_184_, lean_object* v_f_185_, lean_object* v_j_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
v___f_187_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_187_, 0, v_w_183_);
lean_closure_set(v___f_187_, 1, v_f_185_);
lean_closure_set(v___f_187_, 2, v_K_184_);
lean_closure_set(v___f_187_, 3, v_j_186_);
lean_closure_set(v___f_187_, 4, v_inst_181_);
v___x_188_ = lp_mathlib_Finset_sum___redArg(v_inst_180_, v_inst_182_, v___f_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg___boxed(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_w_192_, lean_object* v_K_193_, lean_object* v_f_194_, lean_object* v_j_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg(v_inst_189_, v_inst_190_, v_inst_191_, v_w_192_, v_K_193_, v_f_194_, v_j_195_);
lean_dec_ref(v_inst_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM(lean_object* v_R_197_, lean_object* v_00_u03b9_198_, lean_object* v_00_u03ba_199_, lean_object* v_M_200_, lean_object* v_N_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_w_208_, lean_object* v_K_209_, lean_object* v_f_210_, lean_object* v_j_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg(v_inst_205_, v_inst_206_, v_inst_207_, v_w_208_, v_K_209_, v_f_210_, v_j_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_kerOpM___boxed(lean_object* v_R_213_, lean_object* v_00_u03b9_214_, lean_object* v_00_u03ba_215_, lean_object* v_M_216_, lean_object* v_N_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_w_224_, lean_object* v_K_225_, lean_object* v_f_226_, lean_object* v_j_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_tree_Formalism_ThetaLiftIndependence_kerOpM(v_R_213_, v_00_u03b9_214_, v_00_u03ba_215_, v_M_216_, v_N_217_, v_inst_218_, v_inst_219_, v_inst_220_, v_inst_221_, v_inst_222_, v_inst_223_, v_w_224_, v_K_225_, v_f_226_, v_j_227_);
lean_dec_ref(v_inst_221_);
lean_dec(v_inst_220_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg___boxed(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_w_232_, lean_object* v_K_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg(v_inst_229_, v_inst_230_, v_inst_231_, v_w_232_, v_K_233_, v_x_234_, v_x_235_, v_a_236_);
lean_dec(v_x_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg(lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_w_241_, lean_object* v_K_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_zero_246_; uint8_t v_isZero_247_; 
v_zero_246_ = lean_unsigned_to_nat(0u);
v_isZero_247_ = lean_nat_dec_eq(v_x_243_, v_zero_246_);
if (v_isZero_247_ == 1)
{
lean_object* v___x_248_; 
lean_dec(v_K_242_);
lean_dec(v_w_241_);
lean_dec(v_inst_240_);
lean_dec_ref(v_inst_239_);
lean_dec(v_inst_238_);
v___x_248_ = lean_apply_1(v_x_244_, v_a_245_);
return v___x_248_;
}
else
{
lean_object* v_one_249_; lean_object* v_n_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_one_249_ = lean_unsigned_to_nat(1u);
v_n_250_ = lean_nat_sub(v_x_243_, v_one_249_);
v___x_251_ = lean_nat_add(v_n_250_, v_one_249_);
lean_inc_ref(v_inst_239_);
lean_inc(v___x_251_);
v___x_252_ = lean_apply_1(v_inst_239_, v___x_251_);
lean_inc(v_inst_240_);
v___x_253_ = lean_apply_1(v_inst_240_, v___x_251_);
lean_inc(v_inst_238_);
lean_inc_n(v_n_250_, 3);
v___x_254_ = lean_apply_1(v_inst_238_, v_n_250_);
lean_inc(v_w_241_);
v___x_255_ = lean_apply_1(v_w_241_, v_n_250_);
lean_inc(v_K_242_);
v___x_256_ = lean_apply_1(v_K_242_, v_n_250_);
v___x_257_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg___boxed), 8, 7);
lean_closure_set(v___x_257_, 0, v_inst_238_);
lean_closure_set(v___x_257_, 1, v_inst_239_);
lean_closure_set(v___x_257_, 2, v_inst_240_);
lean_closure_set(v___x_257_, 3, v_w_241_);
lean_closure_set(v___x_257_, 4, v_K_242_);
lean_closure_set(v___x_257_, 5, v_n_250_);
lean_closure_set(v___x_257_, 6, v_x_244_);
v___x_258_ = lp_tree_Formalism_ThetaLiftIndependence_kerOpM___redArg(v___x_252_, v___x_253_, v___x_254_, v___x_255_, v___x_256_, v___x_257_, v_a_245_);
lean_dec_ref(v___x_252_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM(lean_object* v_R_259_, lean_object* v_inst_260_, lean_object* v_00_u03b9_261_, lean_object* v_inst_262_, lean_object* v_M_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_w_266_, lean_object* v_K_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lp_tree_Formalism_ThetaLiftIndependence_chainOpM___redArg(v_inst_262_, v_inst_264_, v_inst_265_, v_w_266_, v_K_267_, v_x_268_, v_x_269_, v_a_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_chainOpM___boxed(lean_object* v_R_272_, lean_object* v_inst_273_, lean_object* v_00_u03b9_274_, lean_object* v_inst_275_, lean_object* v_M_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_w_279_, lean_object* v_K_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_tree_Formalism_ThetaLiftIndependence_chainOpM(v_R_272_, v_inst_273_, v_00_u03b9_274_, v_inst_275_, v_M_276_, v_inst_277_, v_inst_278_, v_w_279_, v_K_280_, v_x_281_, v_x_282_, v_a_283_);
lean_dec(v_x_281_);
lean_dec_ref(v_inst_273_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__0(lean_object* v_val_285_, lean_object* v_property_286_){
_start:
{
lean_inc_ref(v_val_285_);
return v_val_285_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__0___boxed(lean_object* v_val_287_, lean_object* v_property_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__0(v_val_287_, v_property_288_);
lean_dec_ref(v_val_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__1(lean_object* v_00_u03c8_290_, lean_object* v_00_u03c1_291_, lean_object* v_inst_292_, lean_object* v_c_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_val_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_val_295_ = lean_ctor_get(v_c_293_, 0);
lean_inc(v_val_295_);
v___x_296_ = lean_apply_1(v_00_u03c8_290_, v_val_295_);
v___x_297_ = lean_apply_2(v_00_u03c1_291_, v_c_293_, v___y_294_);
v___x_298_ = lean_apply_2(v_inst_292_, v___x_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2(lean_object* v_toMul_299_, lean_object* v_inst_300_, lean_object* v_toOne_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_fst_303_ = lean_ctor_get(v_a_302_, 0);
lean_inc_n(v_fst_303_, 2);
v_snd_304_ = lean_ctor_get(v_a_302_, 1);
lean_inc_n(v_snd_304_, 2);
lean_dec_ref(v_a_302_);
lean_inc(v_toMul_299_);
v___x_305_ = lean_apply_2(v_toMul_299_, v_fst_303_, v_snd_304_);
lean_inc_ref(v_inst_300_);
lean_inc(v_toOne_301_);
v___x_306_ = lean_apply_2(v_inst_300_, v___x_305_, v_toOne_301_);
v___x_307_ = lean_unbox(v___x_306_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; 
lean_dec(v_snd_304_);
lean_dec(v_fst_303_);
lean_dec(v_toOne_301_);
lean_dec_ref(v_inst_300_);
lean_dec(v_toMul_299_);
v___x_308_ = lean_unbox(v___x_306_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_apply_2(v_toMul_299_, v_snd_304_, v_fst_303_);
v___x_310_ = lean_apply_2(v_inst_300_, v___x_309_, v_toOne_301_);
v___x_311_ = lean_unbox(v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2___boxed(lean_object* v_toMul_312_, lean_object* v_inst_313_, lean_object* v_toOne_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2(v_toMul_312_, v_inst_313_, v_toOne_314_, v_a_315_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__3(lean_object* v___x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_toFun_320_; lean_object* v___x_321_; 
v_toFun_320_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_toFun_320_);
lean_dec_ref(v___x_318_);
v___x_321_ = lean_apply_1(v_toFun_320_, v___y_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg(lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_00_u03c8_328_, lean_object* v_00_u03c1_329_){
_start:
{
lean_object* v_toAddMonoid_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_toSemiring_334_; lean_object* v_toMonoid_335_; lean_object* v___x_336_; lean_object* v_toOne_337_; lean_object* v_toMul_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_toAddMonoid_330_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toAddMonoid_330_);
lean_dec_ref(v_inst_326_);
v___x_331_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_330_);
v___x_332_ = lp_mathlib_Field_toSemifield___redArg(v_inst_323_);
v___x_333_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_332_);
v_toSemiring_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_ref(v_toSemiring_334_);
lean_dec_ref(v___x_333_);
v_toMonoid_335_ = lean_ctor_get(v_toSemiring_334_, 1);
lean_inc_ref(v_toMonoid_335_);
lean_dec_ref(v_toSemiring_334_);
v___x_336_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_335_);
v_toOne_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_toOne_337_);
v_toMul_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_toMul_338_);
lean_dec_ref(v___x_336_);
v___f_339_ = ((lean_object*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___closed__0));
v___f_340_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__1), 5, 3);
lean_closure_set(v___f_340_, 0, v_00_u03c8_328_);
lean_closure_set(v___f_340_, 1, v_00_u03c1_329_);
lean_closure_set(v___f_340_, 2, v_inst_327_);
v___f_341_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_341_, 0, v_toMul_338_);
lean_closure_set(v___f_341_, 1, v_inst_325_);
lean_closure_set(v___f_341_, 2, v_toOne_337_);
v___x_342_ = lp_mathlib_unitsEquivProdSubtype(lean_box(0), v_toMonoid_335_);
lean_dec_ref(v_toMonoid_335_);
v___x_343_ = lp_mathlib_Equiv_symm___redArg(v___x_342_);
v___f_344_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__3), 2, 1);
lean_closure_set(v___f_344_, 0, v___x_343_);
lean_inc(v_inst_324_);
v___x_345_ = lp_mathlib_Multiset_product___redArg(v_inst_324_, v_inst_324_);
v___x_346_ = lp_mathlib_Multiset_filter___redArg(v___f_341_, v___x_345_);
v___x_347_ = lp_mathlib_Multiset_pmap___redArg(v___f_339_, v___x_346_);
v___x_348_ = lp_mathlib_Finset_map___redArg(v___f_344_, v___x_347_);
v___x_349_ = lp_mathlib_Finset_sum___redArg(v___x_331_, v___x_348_, v___f_340_);
lean_dec_ref(v___x_331_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___boxed(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_00_u03c8_355_, lean_object* v_00_u03c1_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg(v_inst_350_, v_inst_351_, v_inst_352_, v_inst_353_, v_inst_354_, v_00_u03c8_355_, v_00_u03c1_356_);
lean_dec_ref(v_inst_350_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp(lean_object* v_00_U0001d53d_358_, lean_object* v_V_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_00_u03c8_365_, lean_object* v_00_u03c1_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg(v_inst_360_, v_inst_361_, v_inst_362_, v_inst_363_, v_inst_364_, v_00_u03c8_365_, v_00_u03c1_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOp___boxed(lean_object* v_00_U0001d53d_368_, lean_object* v_V_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_00_u03c8_375_, lean_object* v_00_u03c1_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = lp_tree_Formalism_ThetaLiftIndependence_gaussOp(v_00_U0001d53d_368_, v_V_369_, v_inst_370_, v_inst_371_, v_inst_372_, v_inst_373_, v_inst_374_, v_00_u03c8_375_, v_00_u03c1_376_);
lean_dec_ref(v_inst_370_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual___redArg___lam__3(lean_object* v_toNeg_378_, lean_object* v_00_u03c8_379_, lean_object* v_00_u03c1_380_, lean_object* v_inst_381_, lean_object* v_c_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_val_384_; lean_object* v_inv_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_396_; 
v_val_384_ = lean_ctor_get(v_c_382_, 0);
v_inv_385_ = lean_ctor_get(v_c_382_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_c_382_);
if (v_isSharedCheck_396_ == 0)
{
v___x_387_ = v_c_382_;
v_isShared_388_ = v_isSharedCheck_396_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_inv_385_);
lean_inc(v_val_384_);
lean_dec(v_c_382_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_396_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
lean_inc(v_val_384_);
v___x_389_ = lean_apply_1(v_toNeg_378_, v_val_384_);
v___x_390_ = lean_apply_1(v_00_u03c8_379_, v___x_389_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_val_384_);
lean_ctor_set(v___x_387_, 0, v_inv_385_);
v___x_392_ = v___x_387_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_inv_385_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_val_384_);
v___x_392_ = v_reuseFailAlloc_395_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_apply_2(v_00_u03c1_380_, v___x_392_, v___y_383_);
v___x_394_ = lean_apply_2(v_inst_381_, v___x_390_, v___x_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual___redArg(lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_00_u03c8_402_, lean_object* v_00_u03c1_403_){
_start:
{
lean_object* v_toAddMonoid_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_toSemiring_408_; lean_object* v_toMonoid_409_; lean_object* v___x_410_; lean_object* v_toOne_411_; lean_object* v_toMul_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_toRing_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_toNeg_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___x_428_; 
v_toAddMonoid_404_ = lean_ctor_get(v_inst_400_, 0);
lean_inc_ref(v_toAddMonoid_404_);
lean_dec_ref(v_inst_400_);
v___x_405_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_404_);
v___x_406_ = lp_mathlib_Field_toSemifield___redArg(v_inst_397_);
v___x_407_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_406_);
v_toSemiring_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_toSemiring_408_);
lean_dec_ref(v___x_407_);
v_toMonoid_409_ = lean_ctor_get(v_toSemiring_408_, 1);
lean_inc_ref(v_toMonoid_409_);
lean_dec_ref(v_toSemiring_408_);
v___x_410_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_409_);
v_toOne_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_toOne_411_);
v_toMul_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_toMul_412_);
lean_dec_ref(v___x_410_);
lean_inc(v_inst_398_);
v___x_413_ = lp_mathlib_Multiset_product___redArg(v_inst_398_, v_inst_398_);
v___x_414_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_397_);
v_toRing_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_toRing_415_);
lean_dec_ref(v___x_414_);
v___x_416_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_415_);
lean_dec_ref(v_toRing_415_);
v___x_417_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_416_);
lean_dec_ref(v___x_416_);
v_toNeg_418_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_toNeg_418_);
lean_dec_ref(v___x_417_);
v___f_419_ = ((lean_object*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___closed__0));
v___f_420_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_420_, 0, v_toMul_412_);
lean_closure_set(v___f_420_, 1, v_inst_399_);
lean_closure_set(v___f_420_, 2, v_toOne_411_);
v___x_421_ = lp_mathlib_unitsEquivProdSubtype(lean_box(0), v_toMonoid_409_);
lean_dec_ref(v_toMonoid_409_);
v___x_422_ = lp_mathlib_Equiv_symm___redArg(v___x_421_);
v___f_423_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOp___redArg___lam__3), 2, 1);
lean_closure_set(v___f_423_, 0, v___x_422_);
v___x_424_ = lp_mathlib_Multiset_filter___redArg(v___f_420_, v___x_413_);
v___x_425_ = lp_mathlib_Multiset_pmap___redArg(v___f_419_, v___x_424_);
v___x_426_ = lp_mathlib_Finset_map___redArg(v___f_423_, v___x_425_);
v___f_427_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual___redArg___lam__3), 6, 4);
lean_closure_set(v___f_427_, 0, v_toNeg_418_);
lean_closure_set(v___f_427_, 1, v_00_u03c8_402_);
lean_closure_set(v___f_427_, 2, v_00_u03c1_403_);
lean_closure_set(v___f_427_, 3, v_inst_401_);
v___x_428_ = lp_mathlib_Finset_sum___redArg(v___x_405_, v___x_426_, v___f_427_);
lean_dec_ref(v___x_405_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual(lean_object* v_00_U0001d53d_429_, lean_object* v_V_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_00_u03c8_436_, lean_object* v_00_u03c1_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lp_tree_Formalism_ThetaLiftIndependence_gaussOpDual___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_inst_434_, v_inst_435_, v_00_u03c8_436_, v_00_u03c1_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg(lean_object* v_T_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_zero_442_; uint8_t v_isZero_443_; 
v_zero_442_ = lean_unsigned_to_nat(0u);
v_isZero_443_ = lean_nat_dec_eq(v_x_441_, v_zero_442_);
if (v_isZero_443_ == 1)
{
lean_object* v___f_444_; 
lean_dec(v_T_440_);
v___f_444_ = ((lean_object*)(lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg___closed__0));
return v___f_444_;
}
else
{
lean_object* v_one_445_; lean_object* v_n_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___f_449_; 
v_one_445_ = lean_unsigned_to_nat(1u);
v_n_446_ = lean_nat_sub(v_x_441_, v_one_445_);
lean_inc(v_T_440_);
v___x_447_ = lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg(v_T_440_, v_n_446_);
v___x_448_ = lean_apply_1(v_T_440_, v_n_446_);
v___f_449_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_449_, 0, v___x_448_);
lean_closure_set(v___f_449_, 1, v___x_447_);
return v___f_449_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg___boxed(lean_object* v_T_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg(v_T_450_, v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain(lean_object* v_00_U0001d55c_453_, lean_object* v_inst_454_, lean_object* v_E_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_T_458_, lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lp_tree_Formalism_ThetaLiftIndependence_downChain___redArg(v_T_458_, v_x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_downChain___boxed(lean_object* v_00_U0001d55c_461_, lean_object* v_inst_462_, lean_object* v_E_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_T_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = lp_tree_Formalism_ThetaLiftIndependence_downChain(v_00_U0001d55c_461_, v_inst_462_, v_E_463_, v_inst_464_, v_inst_465_, v_T_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_inst_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_462_);
return v_res_468_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementTheta(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaLiftIndependence_Statement(uint8_t builtin) {
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
res = initialize_tree_Formalism_HermitianLattices_StatementTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
