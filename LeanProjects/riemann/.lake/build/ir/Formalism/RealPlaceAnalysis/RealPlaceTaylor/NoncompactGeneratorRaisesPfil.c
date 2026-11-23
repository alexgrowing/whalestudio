// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementU public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
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
lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_tree_Formalism_REAL_ew___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_u1W___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_u1W(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_u1W___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_u1W___redArg(lean_object* v_E_1_, lean_object* v_j_2_, lean_object* v_00_u03b1_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = l_List_ofFn___redArg(v_j_2_, v_00_u03b1_3_);
v___x_5_ = l_List_reverse___redArg(v___x_4_);
v___x_6_ = lp_tree_Formalism_REAL_ew___redArg(v_E_1_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_u1W(lean_object* v_V_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_n_10_, lean_object* v_E_11_, lean_object* v_j_12_, lean_object* v_00_u03b1_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_REAL_u1W___redArg(v_E_11_, v_j_12_, v_00_u03b1_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_u1W___boxed(lean_object* v_V_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_E_19_, lean_object* v_j_20_, lean_object* v_00_u03b1_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_REAL_u1W(v_V_15_, v_inst_16_, v_inst_17_, v_n_18_, v_E_19_, v_j_20_, v_00_u03b1_21_);
lean_dec(v_n_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementU(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementU(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
