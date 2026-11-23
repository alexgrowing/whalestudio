// Lean compiler output
// Module: Formalism.SizeWindowBrackets.SlopeHypothesesRounded
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.ClaimGaFree public import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Formalism_LFunctionChainParameters_UnitWeightPartition_Ee___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_LFunctionChainParameters_UnitWeightPartition_Ga___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_LFunctionChainParameters_UnitWeightPartition_Fo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ga___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ga(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Fo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Fo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ee___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ee(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ga___redArg(lean_object* v_m_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_S_3_; lean_object* v_l_4_; lean_object* v_gain_5_; lean_object* v_tau_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_S_3_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_S_3_);
v_l_4_ = lean_ctor_get(v_p_2_, 2);
lean_inc(v_l_4_);
v_gain_5_ = lean_ctor_get(v_p_2_, 3);
lean_inc(v_gain_5_);
v_tau_6_ = lean_ctor_get(v_p_2_, 6);
lean_inc(v_tau_6_);
lean_dec_ref(v_p_2_);
v___x_7_ = l_List_finRange(v_m_1_);
v___x_8_ = lp_tree_Formalism_LFunctionChainParameters_UnitWeightPartition_Ga___redArg(v_S_3_, v___x_7_, v_l_4_, v_gain_5_, v_tau_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ga(lean_object* v_00_u03b9_9_, lean_object* v_m_10_, lean_object* v_p_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ga___redArg(v_m_10_, v_p_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Fo___redArg(lean_object* v_m_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_S_15_; lean_object* v_l_16_; lean_object* v_F_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_S_15_ = lean_ctor_get(v_p_14_, 0);
lean_inc(v_S_15_);
v_l_16_ = lean_ctor_get(v_p_14_, 2);
lean_inc(v_l_16_);
v_F_17_ = lean_ctor_get(v_p_14_, 4);
lean_inc(v_F_17_);
lean_dec_ref(v_p_14_);
v___x_18_ = l_List_finRange(v_m_13_);
v___x_19_ = lp_tree_Formalism_LFunctionChainParameters_UnitWeightPartition_Fo___redArg(v_S_15_, v___x_18_, v_l_16_, v_F_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Fo(lean_object* v_00_u03b9_20_, lean_object* v_m_21_, lean_object* v_p_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Fo___redArg(v_m_21_, v_p_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ee___redArg(lean_object* v_m_24_, lean_object* v_p_25_){
_start:
{
lean_object* v_S_26_; lean_object* v_l_27_; lean_object* v_E_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_S_26_ = lean_ctor_get(v_p_25_, 0);
lean_inc(v_S_26_);
v_l_27_ = lean_ctor_get(v_p_25_, 2);
lean_inc(v_l_27_);
v_E_28_ = lean_ctor_get(v_p_25_, 5);
lean_inc(v_E_28_);
lean_dec_ref(v_p_25_);
v___x_29_ = l_List_finRange(v_m_24_);
v___x_30_ = lp_tree_Formalism_LFunctionChainParameters_UnitWeightPartition_Ee___redArg(v_S_26_, v___x_29_, v_l_27_, v_E_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ee(lean_object* v_00_u03b9_31_, lean_object* v_m_32_, lean_object* v_p_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_PData_Ee___redArg(v_m_32_, v_p_33_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ClaimGaFree(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_SlopeHypothesesRounded(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ClaimGaFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
