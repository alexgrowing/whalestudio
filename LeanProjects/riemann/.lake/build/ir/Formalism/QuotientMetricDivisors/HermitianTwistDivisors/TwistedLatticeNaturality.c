// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.DivIntoDualShift public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual
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
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_LinearEquiv_smulOfNeZero___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_restrictScalars___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv___redArg(lean_object* v_inst_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v_toSemiring_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_3_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_4_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_3_);
v_toSemiring_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_5_);
lean_dec_ref(v_toSemiring_5_);
v___x_7_ = lp_mathlib_Pi_Function_module___redArg(v___x_6_);
v___x_8_ = lp_mathlib_LinearEquiv_smulOfNeZero___redArg(v_inst_1_, v___x_7_, v_a_2_);
v___x_9_ = lp_mathlib_LinearEquiv_restrictScalars___redArg(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv___redArg___boxed(lean_object* v_inst_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_DivisionValues_shiftEquiv___redArg(v_inst_10_, v_a_11_);
lean_dec_ref(v_inst_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_d_15_, lean_object* v_a_16_, lean_object* v_ha_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_DivisionValues_shiftEquiv___redArg(v_inst_14_, v_a_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_shiftEquiv___boxed(lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_d_21_, lean_object* v_a_22_, lean_object* v_ha_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_DivisionValues_shiftEquiv(v_K_19_, v_inst_20_, v_d_21_, v_a_22_, v_ha_23_);
lean_dec(v_d_21_);
lean_dec_ref(v_inst_20_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_DivIntoDualShift(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_DivIntoDualShift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
