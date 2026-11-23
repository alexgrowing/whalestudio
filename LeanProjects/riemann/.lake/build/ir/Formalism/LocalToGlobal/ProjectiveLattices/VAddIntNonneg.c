// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone public import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cutR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cutR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_spanIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_spanIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latOf(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_R_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_C_9_, lean_object* v_Vs_10_, lean_object* v_hV_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latOf___boxed(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_R_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_C_21_, lean_object* v_Vs_22_, lean_object* v_hV_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_L2_Pj_latOf(v_K_13_, v_inst_14_, v_inst_15_, v_R_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_C_21_, v_Vs_22_, v_hV_23_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_14_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg___redArg(lean_object* v_w_25_){
_start:
{
lean_object* v_aP_26_; lean_object* v_aM_27_; lean_object* v_n_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_aP_26_ = lean_ctor_get(v_w_25_, 0);
v_aM_27_ = lean_ctor_get(v_w_25_, 1);
v_n_28_ = lean_ctor_get(v_w_25_, 2);
lean_inc(v_n_28_);
lean_inc_ref(v_aM_27_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v_aM_27_);
lean_ctor_set(v___x_29_, 1, v_n_28_);
lean_inc_ref(v_aP_26_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v_aP_26_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg___redArg___boxed(lean_object* v_w_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_L2_Pj_deg___redArg(v_w_31_);
lean_dec_ref(v_w_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg(lean_object* v_D_33_, lean_object* v_j_34_, lean_object* v_w_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_L2_Pj_deg___redArg(v_w_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_deg___boxed(lean_object* v_D_37_, lean_object* v_j_38_, lean_object* v_w_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Pj_deg(v_D_37_, v_j_38_, v_w_39_);
lean_dec_ref(v_w_39_);
lean_dec(v_j_38_);
lean_dec_ref(v_D_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cutR(lean_object* v_D_41_, lean_object* v_K_42_, lean_object* v_inst_43_, lean_object* v_R_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_C_47_, lean_object* v_j_48_, lean_object* v_w_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cutR___boxed(lean_object* v_D_51_, lean_object* v_K_52_, lean_object* v_inst_53_, lean_object* v_R_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_C_57_, lean_object* v_j_58_, lean_object* v_w_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_L2_Pj_cutR(v_D_51_, v_K_52_, v_inst_53_, v_R_54_, v_inst_55_, v_inst_56_, v_C_57_, v_j_58_, v_w_59_);
lean_dec_ref(v_w_59_);
lean_dec(v_j_58_);
lean_dec_ref(v_C_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_D_51_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_spanIn(lean_object* v_D_61_, lean_object* v_K_62_, lean_object* v_inst_63_, lean_object* v_R_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_C_69_, lean_object* v_j_70_, lean_object* v_w_71_, lean_object* v_s_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_spanIn___boxed(lean_object* v_D_74_, lean_object* v_K_75_, lean_object* v_inst_76_, lean_object* v_R_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_C_82_, lean_object* v_j_83_, lean_object* v_w_84_, lean_object* v_s_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_L2_Pj_spanIn(v_D_74_, v_K_75_, v_inst_76_, v_R_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_inst_81_, v_C_82_, v_j_83_, v_w_84_, v_s_85_);
lean_dec_ref(v_w_84_);
lean_dec(v_j_83_);
lean_dec_ref(v_C_82_);
lean_dec_ref(v_inst_80_);
lean_dec_ref(v_inst_79_);
lean_dec_ref(v_inst_78_);
lean_dec_ref(v_inst_76_);
lean_dec_ref(v_D_74_);
return v_res_86_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PartitionExtendByZeroAntitone(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_VAddIntNonneg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PartitionExtendByZeroAntitone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
