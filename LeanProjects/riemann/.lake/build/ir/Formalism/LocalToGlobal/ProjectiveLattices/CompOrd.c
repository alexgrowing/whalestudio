// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.CompData
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ___redArg(lean_object* v_G_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_snd_3_; 
v_snd_3_ = lean_ctor_get(v_G_1_, 1);
lean_inc(v_snd_3_);
lean_dec_ref(v_G_1_);
return v_snd_3_;
}
else
{
lean_object* v_val_4_; lean_object* v_fst_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_15_; 
v_val_4_ = lean_ctor_get(v_x_2_, 0);
v_fst_5_ = lean_ctor_get(v_G_1_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v_G_1_);
if (v_isSharedCheck_15_ == 0)
{
lean_object* v_unused_16_; 
v_unused_16_ = lean_ctor_get(v_G_1_, 1);
lean_dec(v_unused_16_);
v___x_7_ = v_G_1_;
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_fst_5_);
lean_dec(v_G_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_12_; 
v_fst_9_ = lean_ctor_get(v_val_4_, 0);
v_snd_10_ = lean_ctor_get(v_val_4_, 1);
lean_inc(v_snd_10_);
lean_inc(v_fst_9_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_snd_10_);
lean_ctor_set(v___x_7_, 0, v_fst_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_fst_9_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_snd_10_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_1(v_fst_5_, v___x_12_);
return v___x_13_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ___redArg___boxed(lean_object* v_G_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_L2_Pj_exZ___redArg(v_G_17_, v_x_18_);
lean_dec(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ(lean_object* v_E_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_H_24_, lean_object* v_Dw_25_, lean_object* v_G_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_L2_Pj_exZ___redArg(v_G_26_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_exZ___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_H_33_, lean_object* v_Dw_34_, lean_object* v_G_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_L2_Pj_exZ(v_E_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_H_33_, v_Dw_34_, v_G_35_, v_x_36_);
lean_dec(v_x_36_);
lean_dec_ref(v_Dw_34_);
lean_dec_ref(v_H_33_);
lean_dec_ref(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg___redArg(lean_object* v_P_38_){
_start:
{
lean_inc_ref(v_P_38_);
return v_P_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg___redArg___boxed(lean_object* v_P_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Pj_PAlg___redArg(v_P_39_);
lean_dec_ref(v_P_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg(lean_object* v_E_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_H_45_, lean_object* v_Dw_46_, lean_object* v_l_47_, lean_object* v_Xo_48_, lean_object* v_c_49_, lean_object* v_Z_50_, lean_object* v_P_51_){
_start:
{
lean_inc_ref(v_P_51_);
return v_P_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PAlg___boxed(lean_object* v_E_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_H_56_, lean_object* v_Dw_57_, lean_object* v_l_58_, lean_object* v_Xo_59_, lean_object* v_c_60_, lean_object* v_Z_61_, lean_object* v_P_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_tree_Formalism_L2_Pj_PAlg(v_E_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_H_56_, v_Dw_57_, v_l_58_, v_Xo_59_, v_c_60_, v_Z_61_, v_P_62_);
lean_dec_ref(v_P_62_);
lean_dec_ref(v_Xo_59_);
lean_dec_ref(v_l_58_);
lean_dec_ref(v_Dw_57_);
lean_dec_ref(v_H_56_);
lean_dec_ref(v_inst_53_);
return v_res_63_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CompData(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CompData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
