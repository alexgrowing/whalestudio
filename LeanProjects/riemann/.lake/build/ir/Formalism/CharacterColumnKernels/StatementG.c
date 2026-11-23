// Lean compiler output
// Module: Formalism.CharacterColumnKernels.StatementG
// Imports: public import Init public meta import Init public import Formalism.CharacterColumnKernels.Statement
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
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigRect___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigRect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigRect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigRect___redArg(lean_object* v_00_u03c1_1_, lean_object* v_P_2_, lean_object* v_p_3_, lean_object* v_q_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_fst_5_ = lean_ctor_get(v_p_3_, 0);
lean_inc(v_fst_5_);
v_snd_6_ = lean_ctor_get(v_p_3_, 1);
lean_inc(v_snd_6_);
lean_dec_ref(v_p_3_);
v_fst_7_ = lean_ctor_get(v_q_4_, 0);
lean_inc(v_fst_7_);
v_snd_8_ = lean_ctor_get(v_q_4_, 1);
lean_inc(v_snd_8_);
lean_dec_ref(v_q_4_);
v___x_9_ = lean_apply_2(v_P_2_, v_fst_5_, v_fst_7_);
v___x_10_ = lean_apply_3(v_00_u03c1_1_, v___x_9_, v_snd_6_, v_snd_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigRect(lean_object* v_R_11_, lean_object* v_O_12_, lean_object* v_inst_13_, lean_object* v_m_14_, lean_object* v_g_15_, lean_object* v_d_16_, lean_object* v_00_u03c1_17_, lean_object* v_P_18_, lean_object* v_p_19_, lean_object* v_q_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_tree_Formalism_NG_bigRect___redArg(v_00_u03c1_17_, v_P_18_, v_p_19_, v_q_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigRect___boxed(lean_object* v_R_22_, lean_object* v_O_23_, lean_object* v_inst_24_, lean_object* v_m_25_, lean_object* v_g_26_, lean_object* v_d_27_, lean_object* v_00_u03c1_28_, lean_object* v_P_29_, lean_object* v_p_30_, lean_object* v_q_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_NG_bigRect(v_R_22_, v_O_23_, v_inst_24_, v_m_25_, v_g_26_, v_d_27_, v_00_u03c1_28_, v_P_29_, v_p_30_, v_q_31_);
lean_dec_ref(v_inst_24_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CharacterColumnKernels_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CharacterColumnKernels_StatementG(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CharacterColumnKernels_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
