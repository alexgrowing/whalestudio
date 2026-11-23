// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActionLevelMemHolds
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.Statement public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_00_u03c6_3_, lean_object* v_g_4_, lean_object* v_h_5_){
_start:
{
lean_object* v_toMonoid_6_; lean_object* v___x_7_; lean_object* v_toMul_8_; lean_object* v_toMonoid_9_; lean_object* v___x_10_; lean_object* v_toMul_11_; lean_object* v___x_12_; lean_object* v_toOne_13_; lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_25_; 
v_toMonoid_6_ = lean_ctor_get(v_inst_1_, 0);
v___x_7_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_6_);
v_toMul_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toMul_8_);
lean_dec_ref(v___x_7_);
v_toMonoid_9_ = lean_ctor_get(v_inst_2_, 0);
v___x_10_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_9_);
v_toMul_11_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_toMul_11_);
lean_dec_ref(v___x_10_);
v___x_12_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_2_);
v_toOne_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_toOne_13_);
lean_dec_ref(v___x_12_);
v_fst_14_ = lean_ctor_get(v_g_4_, 0);
v_snd_15_ = lean_ctor_get(v_g_4_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_g_4_);
if (v_isSharedCheck_25_ == 0)
{
v___x_17_ = v_g_4_;
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_snd_15_);
lean_inc(v_fst_14_);
lean_dec(v_g_4_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_19_ = lean_apply_2(v_toMul_8_, v_fst_14_, v_h_5_);
v___x_20_ = lean_apply_2(v_toMul_11_, v_snd_15_, v_toOne_13_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_20_);
lean_ctor_set(v___x_17_, 0, v___x_19_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_20_);
v___x_22_ = v_reuseFailAlloc_24_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_1(v_00_u03c6_3_, v___x_22_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK___redArg___boxed(lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_00_u03c6_28_, lean_object* v_g_29_, lean_object* v_h_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_UG_P_psiK___redArg(v_inst_26_, v_inst_27_, v_00_u03c6_28_, v_g_29_, v_h_30_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK(lean_object* v_G_u2081_32_, lean_object* v_G_u2082_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_W_36_, lean_object* v_00_u03c6_37_, lean_object* v_g_38_, lean_object* v_h_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_tree_Formalism_UG_P_psiK___redArg(v_inst_34_, v_inst_35_, v_00_u03c6_37_, v_g_38_, v_h_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_psiK___boxed(lean_object* v_G_u2081_41_, lean_object* v_G_u2082_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_W_45_, lean_object* v_00_u03c6_46_, lean_object* v_g_47_, lean_object* v_h_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_UG_P_psiK(v_G_u2081_41_, v_G_u2082_42_, v_inst_43_, v_inst_44_, v_W_45_, v_00_u03c6_46_, v_g_47_, v_h_48_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
return v_res_49_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActionLevelMemHolds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
