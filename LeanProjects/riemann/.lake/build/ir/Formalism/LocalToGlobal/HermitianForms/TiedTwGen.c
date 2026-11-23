// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.TiedTwGen
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel public import Formalism.LocalToGlobal.HermitianColumns.TiedQC
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_ClsTied_toChart___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_ClsTied_toChart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_ClsTied_toChart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_ClsTied_toChart___redArg(lean_object* v_K_1_){
_start:
{
lean_object* v_lev_2_; lean_object* v_y_3_; lean_object* v_stabI_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_lev_2_ = lean_ctor_get(v_K_1_, 0);
v_y_3_ = lean_ctor_get(v_K_1_, 1);
v_stabI_4_ = lean_ctor_get(v_K_1_, 2);
v_isSharedCheck_11_ = !lean_is_exclusive(v_K_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_6_ = v_K_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_stabI_4_);
lean_inc(v_y_3_);
lean_inc(v_lev_2_);
lean_dec(v_K_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_lev_2_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_y_3_);
lean_ctor_set(v_reuseFailAlloc_10_, 2, v_stabI_4_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_ClsTied_toChart(lean_object* v_D_12_, lean_object* v_u_13_, lean_object* v_i_14_, lean_object* v_hi_15_, lean_object* v_K_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_L2_Forms_ClsTied_toChart___redArg(v_K_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_ClsTied_toChart___boxed(lean_object* v_D_18_, lean_object* v_u_19_, lean_object* v_i_20_, lean_object* v_hi_21_, lean_object* v_K_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_Forms_ClsTied_toChart(v_D_18_, v_u_19_, v_i_20_, v_hi_21_, v_K_22_);
lean_dec(v_i_20_);
lean_dec(v_u_19_);
lean_dec_ref(v_D_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG___redArg(lean_object* v_D_24_, lean_object* v_M_25_, lean_object* v_i_26_, lean_object* v_00_u03c4_27_){
_start:
{
lean_object* v_R_28_; lean_object* v_lam_29_; lean_object* v_t_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___f_37_; 
v_R_28_ = lean_ctor_get(v_D_24_, 0);
v_lam_29_ = lean_ctor_get(v_M_25_, 14);
lean_inc_ref(v_lam_29_);
lean_dec_ref(v_M_25_);
v_t_30_ = lean_ctor_get(v_R_28_, 3);
lean_inc(v_i_26_);
v___x_31_ = lean_apply_2(v_lam_29_, v_i_26_, v_00_u03c4_27_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_add(v_t_30_, v___x_32_);
v___x_34_ = lean_nat_mul(v_i_26_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v_i_26_);
v___x_35_ = lean_nat_shiftr(v___x_34_, v___x_32_);
lean_dec(v___x_34_);
v___x_36_ = lean_nat_to_int(v___x_35_);
v___f_37_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_37_, 0, v___x_31_);
lean_closure_set(v___f_37_, 1, v___x_36_);
return v___f_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG___redArg___boxed(lean_object* v_D_38_, lean_object* v_M_39_, lean_object* v_i_40_, lean_object* v_00_u03c4_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_L2_Forms_lamTG___redArg(v_D_38_, v_M_39_, v_i_40_, v_00_u03c4_41_);
lean_dec_ref(v_D_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG(lean_object* v_D_43_, lean_object* v_u_44_, lean_object* v_C_45_, lean_object* v_A_46_, lean_object* v_P_47_, lean_object* v_M_48_, lean_object* v_i_49_, lean_object* v_00_u03c4_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_L2_Forms_lamTG___redArg(v_D_43_, v_M_48_, v_i_49_, v_00_u03c4_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lamTG___boxed(lean_object* v_D_52_, lean_object* v_u_53_, lean_object* v_C_54_, lean_object* v_A_55_, lean_object* v_P_56_, lean_object* v_M_57_, lean_object* v_i_58_, lean_object* v_00_u03c4_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_L2_Forms_lamTG(v_D_52_, v_u_53_, v_C_54_, v_A_55_, v_P_56_, v_M_57_, v_i_58_, v_00_u03c4_59_);
lean_dec_ref(v_P_56_);
lean_dec_ref(v_A_55_);
lean_dec_ref(v_C_54_);
lean_dec(v_u_53_);
lean_dec_ref(v_D_52_);
return v_res_60_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_RankEqFirstLevel(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_TiedQC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedTwGen(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_RankEqFirstLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_TiedQC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
