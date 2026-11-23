// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.OneGauss
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementU public import Formalism.GaussJetBounds.OneLetterRadius public import Formalism.GaussJetBounds.MonoShapeTop public import Formalism.GaussJetBounds.GaussJetProofs.GField public import Formalism.GaussJetBounds.GaussJetProofs.Transfer public import Formalism.GaussJetBounds.GaussJetProofs.FJEval public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP public import Formalism.GaussJetBounds.GaussJetProofs.Labels public import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___redArg(lean_object* v_inst_1_, lean_object* v_Y_2_, lean_object* v_y_3_, lean_object* v_z_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_22_; 
v_fst_5_ = lean_ctor_get(v_y_3_, 0);
v_snd_6_ = lean_ctor_get(v_y_3_, 1);
v_fst_7_ = lean_ctor_get(v_z_4_, 0);
v_snd_8_ = lean_ctor_get(v_z_4_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_z_4_);
if (v_isSharedCheck_22_ == 0)
{
v___x_10_ = v_z_4_;
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_7_);
lean_dec(v_z_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_eq(v_snd_6_, v_snd_8_);
lean_dec(v_snd_8_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_toSemiring_15_; lean_object* v___x_16_; lean_object* v_toZero_17_; 
lean_del_object(v___x_10_);
lean_dec(v_fst_7_);
lean_dec(v_Y_2_);
v___x_13_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_14_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_13_);
v_toSemiring_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toSemiring_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_15_);
v_toZero_17_ = lean_ctor_get(v___x_16_, 1);
lean_inc(v_toZero_17_);
lean_dec_ref(v___x_16_);
return v_toZero_17_;
}
else
{
lean_object* v___x_19_; 
lean_inc(v_fst_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v_fst_7_);
lean_ctor_set(v___x_10_, 0, v_fst_5_);
v___x_19_ = v___x_10_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_fst_5_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_fst_7_);
v___x_19_ = v_reuseFailAlloc_21_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; 
v___x_20_ = lean_apply_1(v_Y_2_, v___x_19_);
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___redArg___boxed(lean_object* v_inst_23_, lean_object* v_Y_24_, lean_object* v_y_25_, lean_object* v_z_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___redArg(v_inst_23_, v_Y_24_, v_y_25_, v_z_26_);
lean_dec_ref(v_y_25_);
lean_dec_ref(v_inst_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA(lean_object* v_K_28_, lean_object* v_inst_29_, lean_object* v_N0_30_, lean_object* v_N1_31_, lean_object* v_Y_32_, lean_object* v_y_33_, lean_object* v_z_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___redArg(v_inst_29_, v_Y_32_, v_y_33_, v_z_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA___boxed(lean_object* v_K_36_, lean_object* v_inst_37_, lean_object* v_N0_38_, lean_object* v_N1_39_, lean_object* v_Y_40_, lean_object* v_y_41_, lean_object* v_z_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_DworkPowerSeriesWeights_OneGauss_frA(v_K_36_, v_inst_37_, v_N0_38_, v_N1_39_, v_Y_40_, v_y_41_, v_z_42_);
lean_dec_ref(v_y_41_);
lean_dec(v_N1_39_);
lean_dec(v_N0_38_);
lean_dec_ref(v_inst_37_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementU(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_MonoShapeTop(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_GField(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Transfer(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_FJEval(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Labels(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_OneGauss(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementU(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_MonoShapeTop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_GField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Transfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_FJEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Labels(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
