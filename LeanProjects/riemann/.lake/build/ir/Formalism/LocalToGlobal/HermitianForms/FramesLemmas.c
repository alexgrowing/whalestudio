// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.FramesLemmas
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.TiedStep
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
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__0(lean_object* v_y_1_, lean_object* v_00_u03c4_2_, lean_object* v___y_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_3(v_y_1_, v_00_u03c4_2_, v_j_4_, v___y_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__1(lean_object* v_g_6_, lean_object* v_00_u03c4_7_, lean_object* v___y_8_, lean_object* v_j_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_3(v_g_6_, v_00_u03c4_7_, v___y_8_, v_j_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0_spec__0___redArg(lean_object* v_s_11_, lean_object* v_f_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lp_mathlib_Multiset_map___redArg(v_f_12_, v_s_11_);
v___x_14_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0___lam__0(lean_object* v_v_15_, lean_object* v_w_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___x_18_; lean_object* v_re_19_; lean_object* v_im_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_inc(v_i_17_);
v___x_18_ = lean_apply_1(v_v_15_, v_i_17_);
v_re_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_re_19_);
v_im_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_im_20_);
lean_dec_ref(v___x_18_);
v___x_21_ = lean_apply_1(v_w_16_, v_i_17_);
v___x_22_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_19_, v_im_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0(lean_object* v_n_23_, lean_object* v_v_24_, lean_object* v_w_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_26_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_26_, 0, v_v_24_);
lean_closure_set(v___f_26_, 1, v_w_25_);
v___x_27_ = l_List_finRange(v_n_23_);
v___x_28_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0_spec__0___redArg(v___x_27_, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__2(lean_object* v_y_29_, lean_object* v_g_30_, lean_object* v_n_31_, lean_object* v_00_u03c4_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___f_35_; lean_object* v___f_36_; lean_object* v___x_37_; 
lean_inc(v_00_u03c4_32_);
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__0), 4, 3);
lean_closure_set(v___f_35_, 0, v_y_29_);
lean_closure_set(v___f_35_, 1, v_00_u03c4_32_);
lean_closure_set(v___f_35_, 2, v___y_34_);
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__1), 4, 3);
lean_closure_set(v___f_36_, 0, v_g_30_);
lean_closure_set(v___f_36_, 1, v_00_u03c4_32_);
lean_closure_set(v___f_36_, 2, v___y_33_);
v___x_37_ = lp_tree_dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0(v_n_31_, v___f_36_, v___f_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___redArg(lean_object* v_n_38_, lean_object* v_g_39_, lean_object* v_y_40_){
_start:
{
lean_object* v___f_41_; 
v___f_41_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__2), 6, 3);
lean_closure_set(v___f_41_, 0, v_y_40_);
lean_closure_set(v___f_41_, 1, v_g_39_);
lean_closure_set(v___f_41_, 2, v_n_38_);
return v___f_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr(lean_object* v_00_u03b9_42_, lean_object* v_n_43_, lean_object* v_G_44_, lean_object* v_g_45_, lean_object* v_hg_46_, lean_object* v_y_47_){
_start:
{
lean_object* v___f_48_; 
v___f_48_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_Frames_tr___redArg___lam__2), 6, 3);
lean_closure_set(v___f_48_, 0, v_y_47_);
lean_closure_set(v___f_48_, 1, v_g_45_);
lean_closure_set(v___f_48_, 2, v_n_43_);
return v___f_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_Frames_tr___boxed(lean_object* v_00_u03b9_49_, lean_object* v_n_50_, lean_object* v_G_51_, lean_object* v_g_52_, lean_object* v_hg_53_, lean_object* v_y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_L2_Forms_Frames_tr(v_00_u03b9_49_, v_n_50_, v_G_51_, v_g_52_, v_hg_53_, v_y_54_);
lean_dec_ref(v_G_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0_spec__0(lean_object* v_00_u03b9_56_, lean_object* v_s_57_, lean_object* v_f_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_L2_Forms_Frames_tr_spec__0_spec__0___redArg(v_s_57_, v_f_58_);
return v___x_59_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedStep(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_FramesLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedStep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
