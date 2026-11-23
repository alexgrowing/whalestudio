// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataArith
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.HarderNarasimhan.StatementPl public import Formalism.HarderNarasimhan.QuotRealize public import Formalism.HarderNarasimhan.StatementFrame public import Formalism.LatticeLocalGlobal.Statement public import Formalism.LatticeLocalGlobal.LatticeLocalGlobalOfGlobal
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
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DivData_cc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DivData_cc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_A_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___boxed(lean_object* v_K_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_A_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_BasicNotions_HLat_dualL(v_K_7_, v_inst_8_, v_inst_9_, v_inst_10_, v_A_11_);
lean_dec_ref(v_A_11_);
lean_dec(v_inst_10_);
lean_dec_ref(v_inst_8_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DivData_cc(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_Words_17_, lean_object* v_inst_18_, lean_object* v_D_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DivData_cc___boxed(lean_object* v_K_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_Words_25_, lean_object* v_inst_26_, lean_object* v_D_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_BasicNotions_DivData_cc(v_K_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_Words_25_, v_inst_26_, v_D_27_);
lean_dec_ref(v_D_27_);
lean_dec(v_inst_26_);
lean_dec(v_inst_24_);
lean_dec_ref(v_inst_22_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_StatementPl(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_QuotRealize(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_StatementFrame(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeLocalGlobal_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeLocalGlobal_LatticeLocalGlobalOfGlobal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_StatementPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_QuotRealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_StatementFrame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeLocalGlobal_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeLocalGlobal_LatticeLocalGlobalOfGlobal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
