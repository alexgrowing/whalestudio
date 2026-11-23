// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsLoc
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsFF public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
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
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_tree_Formalism_UG_diagJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_tjcosets__dG___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_tjcosets__dG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_tjcosets__dG___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_j_3_, lean_object* v_00_u03d6_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toInv_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_19_; 
v___x_5_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_6_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_5_);
lean_dec_ref(v___x_5_);
v___x_7_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_6_);
v___x_8_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_7_);
lean_dec_ref(v___x_7_);
v_toInv_9_ = lean_ctor_get(v___x_8_, 1);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_8_, 0);
lean_dec(v_unused_20_);
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_toInv_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_j_3_);
lean_inc(v_00_u03d6_4_);
lean_inc(v_n_2_);
lean_inc_ref(v_inst_1_);
v___x_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_diagJ), 7, 5);
lean_closure_set(v___x_13_, 0, lean_box(0));
lean_closure_set(v___x_13_, 1, v_inst_1_);
lean_closure_set(v___x_13_, 2, v_n_2_);
lean_closure_set(v___x_13_, 3, v_00_u03d6_4_);
lean_closure_set(v___x_13_, 4, v_j_3_);
v___x_14_ = lean_apply_1(v_toInv_9_, v_00_u03d6_4_);
v___x_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_diagJ), 7, 5);
lean_closure_set(v___x_15_, 0, lean_box(0));
lean_closure_set(v___x_15_, 1, v_inst_1_);
lean_closure_set(v___x_15_, 2, v_n_2_);
lean_closure_set(v___x_15_, 3, v___x_14_);
lean_closure_set(v___x_15_, 4, v_j_3_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___x_15_);
lean_ctor_set(v___x_11_, 0, v___x_13_);
v___x_17_ = v___x_11_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_tjcosets__dG(lean_object* v_L_21_, lean_object* v_inst_22_, lean_object* v_n_23_, lean_object* v_j_24_, lean_object* v_00_u03d6_25_, lean_object* v_h_u03d6_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_UG_P_tjcosets__dG___redArg(v_inst_22_, v_n_23_, v_j_24_, v_00_u03d6_25_);
return v___x_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
