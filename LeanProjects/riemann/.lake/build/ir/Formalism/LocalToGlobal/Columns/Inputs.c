// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.Inputs
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.HeckeSp public import Formalism.LocalToGlobal.Columns.StdLatUnimodular public import Formalism.LocalToGlobal.Columns.Adelic public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice public import Formalism.LogVandermondeBounds.LogRatioLowerBound public import Formalism.GradedWeylDivisibility.StatementD public import Formalism.HermitianLattices.StatementMass public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wSeq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_q_3_, lean_object* v_a_4_, lean_object* v_y_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toSemiring_8_; lean_object* v___x_9_; lean_object* v_toMonoid_10_; lean_object* v_toMul_11_; lean_object* v_toNPow_12_; lean_object* v___x_13_; lean_object* v_toRing_14_; lean_object* v___x_15_; lean_object* v_toAddMonoidWithOne_16_; lean_object* v_toNatCast_17_; lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_6_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_7_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_6_);
v_toSemiring_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref_n(v_toSemiring_8_, 2);
lean_dec_ref(v___x_7_);
v___x_9_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_8_);
v_toMonoid_10_ = lean_ctor_get(v_toSemiring_8_, 1);
lean_inc_ref(v_toMonoid_10_);
lean_dec_ref(v_toSemiring_8_);
v_toMul_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_toMul_11_);
lean_dec_ref(v___x_9_);
v_toNPow_12_ = lean_ctor_get(v_toMonoid_10_, 2);
lean_inc(v_toNPow_12_);
lean_dec_ref(v_toMonoid_10_);
v___x_13_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v_toRing_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref(v_toRing_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_14_);
v_toAddMonoidWithOne_16_ = lean_ctor_get(v___x_15_, 1);
lean_inc_ref(v_toAddMonoidWithOne_16_);
lean_dec_ref(v___x_15_);
v_toNatCast_17_ = lean_ctor_get(v_toAddMonoidWithOne_16_, 0);
lean_inc(v_toNatCast_17_);
lean_dec_ref(v_toAddMonoidWithOne_16_);
v_fst_18_ = lean_ctor_get(v_y_5_, 0);
v_snd_19_ = lean_ctor_get(v_y_5_, 1);
lean_inc(v_fst_18_);
v___x_20_ = lean_apply_1(v_q_3_, v_fst_18_);
v___x_21_ = lean_apply_1(v_toNatCast_17_, v___x_20_);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_sub(v_n_2_, v___x_22_);
v___x_24_ = lean_nat_mul(v_snd_19_, v___x_23_);
lean_dec(v___x_23_);
v___x_25_ = lean_apply_2(v_toNPow_12_, v___x_24_, v___x_21_);
v___x_26_ = lean_apply_1(v_a_4_, v_y_5_);
v___x_27_ = lean_apply_2(v_toMul_11_, v___x_25_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm___redArg___boxed(lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_q_30_, lean_object* v_a_31_, lean_object* v_y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_Formalism_L2_Col_heckeRenorm___redArg(v_inst_28_, v_n_29_, v_q_30_, v_a_31_, v_y_32_);
lean_dec(v_n_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm(lean_object* v_L_34_, lean_object* v_Pl_35_, lean_object* v_inst_36_, lean_object* v_n_37_, lean_object* v_q_38_, lean_object* v_a_39_, lean_object* v_y_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Formalism_L2_Col_heckeRenorm___redArg(v_inst_36_, v_n_37_, v_q_38_, v_a_39_, v_y_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_heckeRenorm___boxed(lean_object* v_L_42_, lean_object* v_Pl_43_, lean_object* v_inst_44_, lean_object* v_n_45_, lean_object* v_q_46_, lean_object* v_a_47_, lean_object* v_y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_L2_Col_heckeRenorm(v_L_42_, v_Pl_43_, v_inst_44_, v_n_45_, v_q_46_, v_a_47_, v_y_48_);
lean_dec(v_n_45_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wSeq(lean_object* v_n_50_, lean_object* v_lam_51_, lean_object* v_i_52_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_nat_dec_lt(v_i_52_, v_n_50_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec(v_i_52_);
lean_dec_ref(v_lam_51_);
v___x_54_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___f_59_; 
lean_inc(v_i_52_);
v___x_55_ = lean_apply_1(v_lam_51_, v_i_52_);
v___x_56_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_55_);
v___x_57_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_i_52_);
v___f_58_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_58_, 0, v___x_57_);
v___f_59_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_59_, 0, v___x_56_);
lean_closure_set(v___f_59_, 1, v___f_58_);
return v___f_59_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wSeq___boxed(lean_object* v_n_60_, lean_object* v_lam_61_, lean_object* v_i_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_tree_Formalism_L2_Col_wSeq(v_n_60_, v_lam_61_, v_i_62_);
lean_dec(v_n_60_);
return v_res_63_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_Adelic(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ScaledRamifiedLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogVandermondeBounds_LogRatioLowerBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementD(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementMass(uint8_t builtin);
lean_object* initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_RelevantZeroGramTerms(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_Inputs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_Adelic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ScaledRamifiedLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogVandermondeBounds_LogRatioLowerBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementMass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_RelevantZeroGramTerms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
