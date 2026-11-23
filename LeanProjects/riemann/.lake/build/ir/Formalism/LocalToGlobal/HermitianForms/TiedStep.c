// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.TiedStep
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter public import Formalism.LocalToGlobal.HermitianForms.DetShiftShW
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamT(lean_object* v_D_1_, lean_object* v_u_2_, lean_object* v_i_3_, lean_object* v_00_u03c4_4_){
_start:
{
lean_object* v_R_5_; lean_object* v_fm_6_; lean_object* v___x_7_; lean_object* v_lam_8_; lean_object* v_t_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___f_16_; 
v_R_5_ = lean_ctor_get(v_D_1_, 0);
lean_inc_ref(v_R_5_);
v_fm_6_ = lean_ctor_get(v_D_1_, 50);
lean_inc_ref(v_fm_6_);
lean_dec_ref(v_D_1_);
v___x_7_ = lean_apply_1(v_fm_6_, v_u_2_);
v_lam_8_ = lean_ctor_get(v___x_7_, 14);
lean_inc_ref(v_lam_8_);
lean_dec_ref(v___x_7_);
v_t_9_ = lean_ctor_get(v_R_5_, 3);
lean_inc(v_t_9_);
lean_dec_ref(v_R_5_);
lean_inc(v_i_3_);
v___x_10_ = lean_apply_2(v_lam_8_, v_i_3_, v_00_u03c4_4_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_t_9_, v___x_11_);
lean_dec(v_t_9_);
v___x_13_ = lean_nat_mul(v_i_3_, v___x_12_);
lean_dec(v___x_12_);
lean_dec(v_i_3_);
v___x_14_ = lean_nat_shiftr(v___x_13_, v___x_11_);
lean_dec(v___x_13_);
v___x_15_ = lean_nat_to_int(v___x_14_);
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_16_, 0, v___x_10_);
lean_closure_set(v___f_16_, 1, v___x_15_);
return v___f_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_PsiZeroNontrivialCharacter(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_DetShiftShW(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedStep(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_PsiZeroNontrivialCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_DetShiftShW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
