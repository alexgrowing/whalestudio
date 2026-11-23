// Lean compiler output
// Module: Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
// Imports: public import Init public meta import Init public import Formalism.HarderNarasimhan.QuotRealize public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_QuotientRealization_pv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_QuotientRealization_pv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_QuotientRealization_pv(lean_object* v_K_1_, lean_object* v_V_2_, lean_object* v_00_u03b9_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_b_9_, lean_object* v_X_10_, lean_object* v_U_11_, lean_object* v_v_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_QuotientRealization_pv___boxed(lean_object* v_K_14_, lean_object* v_V_15_, lean_object* v_00_u03b9_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_b_22_, lean_object* v_X_23_, lean_object* v_U_24_, lean_object* v_v_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_HN_QuotientRealization_pv(v_K_14_, v_V_15_, v_00_u03b9_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_b_22_, v_X_23_, v_U_24_, v_v_25_);
lean_dec(v_v_25_);
lean_dec_ref(v_X_23_);
lean_dec_ref(v_b_22_);
lean_dec_ref(v_inst_21_);
lean_dec(v_inst_20_);
lean_dec(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_QuotRealize(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_QuotRealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
