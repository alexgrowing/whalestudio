// Lean compiler output
// Module: Formalism.LocalToGlobal.KernelLattices.LateralTheory
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3 public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_prod___at___00Formalism_L2_Th1_H_tens4_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_powLat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_powLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_lamMM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_lamMM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Base_lamM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Base_lamM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__0(lean_object* v_z_1_, lean_object* v_i_2_, lean_object* v_j_3_, lean_object* v_00_u03c4_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_3(v_z_1_, v_00_u03c4_4_, v_i_2_, v_j_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__1(lean_object* v_z_6_, lean_object* v_i_7_, lean_object* v_00_u03b8_8_, lean_object* v_j_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; 
v___f_10_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__0), 4, 3);
lean_closure_set(v___f_10_, 0, v_z_6_);
lean_closure_set(v___f_10_, 1, v_i_7_);
lean_closure_set(v___f_10_, 2, v_j_9_);
v___x_11_ = lean_apply_1(v_00_u03b8_8_, v___f_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__2(lean_object* v_z_12_, lean_object* v_00_u03b8_13_, lean_object* v_N_14_, lean_object* v_i_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__1), 4, 3);
lean_closure_set(v___f_16_, 0, v_z_12_);
lean_closure_set(v___f_16_, 1, v_i_15_);
lean_closure_set(v___f_16_, 2, v_00_u03b8_13_);
v___x_17_ = l_List_finRange(v_N_14_);
v___x_18_ = lp_tree_Finset_prod___at___00Formalism_L2_Th1_H_tens4_spec__0___redArg(v___x_17_, v___f_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow___redArg(lean_object* v_00_u03b8_19_, lean_object* v_N_20_, lean_object* v_N_x27_21_, lean_object* v_z_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_tensPow___redArg___lam__2), 4, 3);
lean_closure_set(v___f_23_, 0, v_z_22_);
lean_closure_set(v___f_23_, 1, v_00_u03b8_19_);
lean_closure_set(v___f_23_, 2, v_N_20_);
v___x_24_ = l_List_finRange(v_N_x27_21_);
v___x_25_ = lp_tree_Finset_prod___at___00Formalism_L2_Th1_H_tens4_spec__0___redArg(v___x_24_, v___f_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_tensPow(lean_object* v_n_26_, lean_object* v_00_u03b8_27_, lean_object* v_N_28_, lean_object* v_N_x27_29_, lean_object* v_z_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_Formalism_L2_Ker_tensPow___redArg(v_00_u03b8_27_, v_N_28_, v_N_x27_29_, v_z_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_powLat(lean_object* v_n_32_, lean_object* v_00_u039bM_33_, lean_object* v_N_34_, lean_object* v_N_x27_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_powLat___boxed(lean_object* v_n_37_, lean_object* v_00_u039bM_38_, lean_object* v_N_39_, lean_object* v_N_x27_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_L2_Ker_powLat(v_n_37_, v_00_u039bM_38_, v_N_39_, v_N_x27_40_);
lean_dec(v_N_x27_40_);
lean_dec(v_N_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__1(lean_object* v_00_u03b9_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__1___boxed(lean_object* v_00_u03b9_45_, lean_object* v_s_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__1(v_00_u03b9_45_, v_s_46_);
lean_dec_ref(v_s_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__2(lean_object* v_S_48_, lean_object* v_s_49_, lean_object* v_hs_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0___lam__0(lean_object* v_S_52_, lean_object* v_h_53_){
_start:
{
return v_S_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__0(lean_object* v_00_u03b9_54_, lean_object* v_s_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__0___boxed(lean_object* v_00_u03b9_57_, lean_object* v_s_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0_spec__0(v_00_u03b9_57_, v_s_58_);
lean_dec_ref(v_s_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0___lam__1(lean_object* v_S_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_L2_Ker_lamMM_spec__0(lean_object* v_k_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_lamMM(lean_object* v_D_64_, lean_object* v_00_u039b_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_lamMM___boxed(lean_object* v_D_67_, lean_object* v_00_u039b_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Formalism_L2_Ker_lamMM(v_D_67_, v_00_u039b_68_);
lean_dec_ref(v_D_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Base_lamM(lean_object* v_D_70_, lean_object* v_cc_71_, lean_object* v_00_u03b4_72_, lean_object* v___B_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_Base_lamM___boxed(lean_object* v_D_75_, lean_object* v_cc_76_, lean_object* v_00_u03b4_77_, lean_object* v___B_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Formalism_L2_Ker_Base_lamM(v_D_75_, v_cc_76_, v_00_u03b4_77_, v___B_78_);
lean_dec_ref(v___B_78_);
lean_dec_ref(v_00_u03b4_77_);
lean_dec_ref(v_D_75_);
return v_res_79_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_TaylorLogMetric(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GL3Theta(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_StandardLatticesGL3(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_KernelLattices_LateralTheory(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_TaylorLogMetric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GL3Theta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_StandardLatticesGL3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
