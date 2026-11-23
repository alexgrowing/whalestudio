// Lean compiler output
// Module: Formalism.SizeWindowBrackets.CutFailsForRSubmodule
// Imports: public import Init public meta import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_latV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_latV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_cutN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_cutN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_latV(lean_object* v_R_1_, lean_object* v_K_2_, lean_object* v_W_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_M_11_, lean_object* v_V_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_latV___boxed(lean_object* v_R_14_, lean_object* v_K_15_, lean_object* v_W_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_M_24_, lean_object* v_V_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_latV(v_R_14_, v_K_15_, v_W_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_M_24_, v_V_25_);
lean_dec(v_inst_22_);
lean_dec(v_inst_21_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_cutN(lean_object* v_R_27_, lean_object* v_K_28_, lean_object* v_W_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_00_u03d6_37_, lean_object* v_00_u03c4_38_, lean_object* v_M_39_, lean_object* v_N_40_, lean_object* v_V_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_cutN___boxed(lean_object* v_R_43_, lean_object* v_K_44_, lean_object* v_W_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_00_u03d6_53_, lean_object* v_00_u03c4_54_, lean_object* v_M_55_, lean_object* v_N_56_, lean_object* v_V_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_LFunctionChainParameters_DiagonalSublatticeLength_cutN(v_R_43_, v_K_44_, v_W_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_, v_00_u03d6_53_, v_00_u03c4_54_, v_M_55_, v_N_56_, v_V_57_);
lean_dec(v_00_u03c4_54_);
lean_dec(v_00_u03d6_53_);
lean_dec(v_inst_51_);
lean_dec(v_inst_50_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_CutFailsForRSubmodule(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
