// Lean compiler output
// Module: Formalism.RankGapBounds.MeanBoundSecondForm
// Imports: public import Init public meta import Init public import Mathlib
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
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_instNatCast;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_8__overap_3_; lean_object* v___x_4_; 
v___x_2_ = l_List_lengthTR___redArg(v_inst_1_);
v___x_8__overap_3_ = lp_mathlib_Real_instNatCast;
v___x_4_ = lean_apply_1(v___x_8__overap_3_, v___x_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___redArg___boxed(lean_object* v_inst_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___redArg(v_inst_5_);
lean_dec(v_inst_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT(lean_object* v_U0_7_, lean_object* v_W_8_, lean_object* v_Top_9_, lean_object* v_inst_10_, lean_object* v_m_11_, lean_object* v_f_12_, lean_object* v_x_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___redArg(v_inst_10_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT___boxed(lean_object* v_U0_15_, lean_object* v_W_16_, lean_object* v_Top_17_, lean_object* v_inst_18_, lean_object* v_m_19_, lean_object* v_f_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_nT(v_U0_15_, v_W_16_, v_Top_17_, v_inst_18_, v_m_19_, v_f_20_, v_x_21_);
lean_dec_ref(v_x_21_);
lean_dec(v_f_20_);
lean_dec(v_m_19_);
lean_dec(v_inst_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___redArg___lam__0(lean_object* v_D_23_, lean_object* v_t_24_){
_start:
{
lean_object* v_aT_25_; lean_object* v___x_26_; 
v_aT_25_ = lean_ctor_get(v_D_23_, 15);
lean_inc(v_aT_25_);
lean_dec_ref(v_D_23_);
v___x_26_ = lean_apply_1(v_aT_25_, v_t_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___redArg(lean_object* v_inst_27_, lean_object* v_D_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___redArg___lam__0), 2, 1);
lean_closure_set(v___f_29_, 0, v_D_28_);
v___x_30_ = lp_mathlib_Real_instAddCommMonoid;
v___x_31_ = lp_mathlib_Finset_sum___redArg(v___x_30_, v_inst_27_, v___f_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA(lean_object* v_U0_32_, lean_object* v_W_33_, lean_object* v_Top_34_, lean_object* v_inst_35_, lean_object* v_m_36_, lean_object* v_f_37_, lean_object* v_D_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___redArg(v_inst_35_, v_D_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA___boxed(lean_object* v_U0_40_, lean_object* v_W_41_, lean_object* v_Top_42_, lean_object* v_inst_43_, lean_object* v_m_44_, lean_object* v_f_45_, lean_object* v_D_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_sumA(v_U0_40_, v_W_41_, v_Top_42_, v_inst_43_, v_m_44_, v_f_45_, v_D_46_);
lean_dec(v_f_45_);
lean_dec(v_m_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___redArg___lam__0(lean_object* v_D_48_, lean_object* v_u0_49_, lean_object* v_u_50_, lean_object* v_j_51_){
_start:
{
lean_object* v_EeJ_52_; lean_object* v___x_53_; 
v_EeJ_52_ = lean_ctor_get(v_D_48_, 24);
lean_inc(v_EeJ_52_);
lean_dec_ref(v_D_48_);
v___x_53_ = lean_apply_3(v_EeJ_52_, v_u0_49_, v_u_50_, v_j_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___redArg(lean_object* v_m_54_, lean_object* v_D_55_, lean_object* v_u0_56_, lean_object* v_u_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_58_ = lean_alloc_closure((void*)(lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___redArg___lam__0), 4, 3);
lean_closure_set(v___f_58_, 0, v_D_55_);
lean_closure_set(v___f_58_, 1, v_u0_56_);
lean_closure_set(v___f_58_, 2, v_u_57_);
v___x_59_ = l_List_finRange(v_m_54_);
v___x_60_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_59_, v___f_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee(lean_object* v_U0_61_, lean_object* v_W_62_, lean_object* v_Top_63_, lean_object* v_m_64_, lean_object* v_f_65_, lean_object* v_D_66_, lean_object* v_u0_67_, lean_object* v_u_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___redArg(v_m_64_, v_D_66_, v_u0_67_, v_u_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee___boxed(lean_object* v_U0_70_, lean_object* v_W_71_, lean_object* v_Top_72_, lean_object* v_m_73_, lean_object* v_f_74_, lean_object* v_D_75_, lean_object* v_u0_76_, lean_object* v_u_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_tree_Formalism_RankGapBounds_WeightedMeanData_Data_Ee(v_U0_70_, v_W_71_, v_Top_72_, v_m_73_, v_f_74_, v_D_75_, v_u0_76_, v_u_77_);
lean_dec(v_f_74_);
return v_res_78_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RankGapBounds_MeanBoundSecondForm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
