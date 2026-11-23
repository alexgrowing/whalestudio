// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex___redArg(lean_object* v_a_1_, lean_object* v_n_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_dec_ref(v_a_1_);
lean_inc(v_n_2_);
return v_n_2_;
}
else
{
lean_object* v_val_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_14_; 
v_val_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v_x_3_, 1);
v_fst_5_ = lean_ctor_get(v_val_4_, 0);
v_snd_6_ = lean_ctor_get(v_val_4_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_val_4_);
if (v_isSharedCheck_14_ == 0)
{
v___x_8_ = v_val_4_;
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
lean_dec(v_val_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_11_; 
if (v_isShared_9_ == 0)
{
v___x_11_ = v___x_8_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_fst_5_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_snd_6_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_1(v_a_1_, v___x_11_);
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex___redArg___boxed(lean_object* v_a_15_, lean_object* v_n_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Pj_ex___redArg(v_a_15_, v_n_16_, v_x_17_);
lean_dec(v_n_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex(lean_object* v_E_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_H_23_, lean_object* v_Dw_24_, lean_object* v_a_25_, lean_object* v_n_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_L2_Pj_ex___redArg(v_a_25_, v_n_26_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ex___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_H_33_, lean_object* v_Dw_34_, lean_object* v_a_35_, lean_object* v_n_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_L2_Pj_ex(v_E_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_H_33_, v_Dw_34_, v_a_35_, v_n_36_, v_x_37_);
lean_dec(v_n_36_);
lean_dec_ref(v_Dw_34_);
lean_dec_ref(v_H_33_);
lean_dec_ref(v_inst_30_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
