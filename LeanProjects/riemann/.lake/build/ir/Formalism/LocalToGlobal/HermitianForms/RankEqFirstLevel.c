// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianColumns.StarConj public import Formalism.LocalToGlobal.HermitianForms.FormsTied public import Formalism.LocalToGlobal.HermitianForms.DefsChi
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
lean_object* lp_mathlib_finCongr(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_mapEquiv___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_LinearEquiv_funCongrLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL___redArg(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lp_mathlib_finCongr(v_a_1_, v_b_2_, lean_box(0));
lean_inc_ref(v___x_3_);
v___x_4_ = lp_mathlib_Matrix_reindex___redArg(v___x_3_, v___x_3_);
v___x_5_ = lp_mathlib_Units_mapEquiv___redArg(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL___redArg___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_L2_Forms_reGL___redArg(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL(lean_object* v_a_9_, lean_object* v_b_10_, lean_object* v_h_11_, lean_object* v_R_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_L2_Forms_reGL___redArg(v_a_9_, v_b_10_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reGL___boxed(lean_object* v_a_15_, lean_object* v_b_16_, lean_object* v_h_17_, lean_object* v_R_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_Forms_reGL(v_a_15_, v_b_16_, v_h_17_, v_R_18_, v_inst_19_);
lean_dec_ref(v_inst_19_);
lean_dec(v_b_16_);
lean_dec(v_a_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV___redArg(lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lp_mathlib_finCongr(v_a_21_, v_b_22_, lean_box(0));
v___x_24_ = lp_mathlib_Equiv_symm___redArg(v___x_23_);
v___x_25_ = lp_mathlib_LinearEquiv_funCongrLeft___redArg(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV___redArg___boxed(lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_L2_Forms_reV___redArg(v_a_26_, v_b_27_);
lean_dec(v_b_27_);
lean_dec(v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV(lean_object* v_a_29_, lean_object* v_b_30_, lean_object* v_h_31_, lean_object* v_E_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_L2_Forms_reV___redArg(v_a_29_, v_b_30_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reV___boxed(lean_object* v_a_35_, lean_object* v_b_36_, lean_object* v_h_37_, lean_object* v_E_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Forms_reV(v_a_35_, v_b_36_, v_h_37_, v_E_38_, v_inst_39_);
lean_dec_ref(v_inst_39_);
lean_dec(v_b_36_);
lean_dec(v_a_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reL(lean_object* v_a_41_, lean_object* v_b_42_, lean_object* v_h_43_, lean_object* v_E_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_L_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_reL___boxed(lean_object* v_a_49_, lean_object* v_b_50_, lean_object* v_h_51_, lean_object* v_E_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_L_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_Formalism_L2_Forms_reL(v_a_49_, v_b_50_, v_h_51_, v_E_52_, v_inst_53_, v_inst_54_, v_L_55_);
lean_dec_ref(v_inst_53_);
lean_dec(v_b_50_);
lean_dec(v_a_49_);
return v_res_56_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_StarConj(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_FormsTied(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_DefsChi(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_RankEqFirstLevel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_StarConj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_FormsTied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_DefsChi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
