// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementE public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
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
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_heckecomm__tr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_heckecomm__tr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_heckecomm__tr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_heckecomm__tr___redArg(lean_object* v_g_1_){
_start:
{
lean_object* v_val_2_; lean_object* v_inv_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_12_; 
v_val_2_ = lean_ctor_get(v_g_1_, 0);
v_inv_3_ = lean_ctor_get(v_g_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_g_1_);
if (v_isSharedCheck_12_ == 0)
{
v___x_5_ = v_g_1_;
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_inv_3_);
lean_inc(v_val_2_);
lean_dec(v_g_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_7_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_7_, 0, lean_box(0));
lean_closure_set(v___x_7_, 1, lean_box(0));
lean_closure_set(v___x_7_, 2, lean_box(0));
lean_closure_set(v___x_7_, 3, v_val_2_);
v___x_8_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_8_, 0, lean_box(0));
lean_closure_set(v___x_8_, 1, lean_box(0));
lean_closure_set(v___x_8_, 2, lean_box(0));
lean_closure_set(v___x_8_, 3, v_inv_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v___x_8_);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_10_ = v___x_5_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v___x_8_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_heckecomm__tr(lean_object* v_R_13_, lean_object* v_inst_14_, lean_object* v_n_15_, lean_object* v_g_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_UG_P_heckecomm__tr___redArg(v_g_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_heckecomm__tr___boxed(lean_object* v_R_18_, lean_object* v_inst_19_, lean_object* v_n_20_, lean_object* v_g_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_UG_P_heckecomm__tr(v_R_18_, v_inst_19_, v_n_20_, v_g_21_);
lean_dec(v_n_20_);
lean_dec_ref(v_inst_19_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementE(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
