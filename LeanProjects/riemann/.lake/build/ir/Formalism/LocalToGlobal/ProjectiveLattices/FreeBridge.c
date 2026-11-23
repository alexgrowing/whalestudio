// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal public import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree public import Formalism.LocalToGlobal.ProjectiveLattices.PtFree public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_ofPj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_ofPj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_ofPj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_toPj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_toPj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_toPj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_ofPj___redArg(lean_object* v_U_1_){
_start:
{
lean_object* v_fin_2_; lean_object* v_X_3_; lean_object* v_un_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_fin_2_ = lean_ctor_get(v_U_1_, 0);
v_X_3_ = lean_ctor_get(v_U_1_, 1);
v_un_4_ = lean_ctor_get(v_U_1_, 2);
v_isSharedCheck_11_ = !lean_is_exclusive(v_U_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_6_ = v_U_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_un_4_);
lean_inc(v_X_3_);
lean_inc(v_fin_2_);
lean_dec(v_U_1_);
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
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_fin_2_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_X_3_);
lean_ctor_set(v_reuseFailAlloc_10_, 2, v_un_4_);
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_ofPj(lean_object* v_E_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_H_16_, lean_object* v_Dw_17_, lean_object* v_l_18_, lean_object* v_Xo_19_, lean_object* v_c_20_, lean_object* v_00_u03c3_21_, lean_object* v_r_22_, lean_object* v_U_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_tree_Formalism_L2_PjFree_Unf_ofPj___redArg(v_U_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_ofPj___boxed(lean_object* v_E_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_H_29_, lean_object* v_Dw_30_, lean_object* v_l_31_, lean_object* v_Xo_32_, lean_object* v_c_33_, lean_object* v_00_u03c3_34_, lean_object* v_r_35_, lean_object* v_U_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_L2_PjFree_Unf_ofPj(v_E_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_H_29_, v_Dw_30_, v_l_31_, v_Xo_32_, v_c_33_, v_00_u03c3_34_, v_r_35_, v_U_36_);
lean_dec(v_r_35_);
lean_dec_ref(v_00_u03c3_34_);
lean_dec_ref(v_Xo_32_);
lean_dec_ref(v_l_31_);
lean_dec_ref(v_Dw_30_);
lean_dec_ref(v_H_29_);
lean_dec_ref(v_inst_26_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_toPj___redArg(lean_object* v_U_38_){
_start:
{
lean_object* v_fin_39_; lean_object* v_X_40_; lean_object* v_un_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_fin_39_ = lean_ctor_get(v_U_38_, 0);
v_X_40_ = lean_ctor_get(v_U_38_, 1);
v_un_41_ = lean_ctor_get(v_U_38_, 2);
v_isSharedCheck_48_ = !lean_is_exclusive(v_U_38_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v_U_38_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_un_41_);
lean_inc(v_X_40_);
lean_inc(v_fin_39_);
lean_dec(v_U_38_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_fin_39_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_X_40_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v_un_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_toPj(lean_object* v_E_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_H_53_, lean_object* v_Dw_54_, lean_object* v_l_55_, lean_object* v_Xo_56_, lean_object* v_c_57_, lean_object* v_00_u03c3_58_, lean_object* v_r_59_, lean_object* v_U_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_tree_Formalism_L2_PjFree_Unf_toPj___redArg(v_U_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_Unf_toPj___boxed(lean_object* v_E_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_H_66_, lean_object* v_Dw_67_, lean_object* v_l_68_, lean_object* v_Xo_69_, lean_object* v_c_70_, lean_object* v_00_u03c3_71_, lean_object* v_r_72_, lean_object* v_U_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_L2_PjFree_Unf_toPj(v_E_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_H_66_, v_Dw_67_, v_l_68_, v_Xo_69_, v_c_70_, v_00_u03c3_71_, v_r_72_, v_U_73_);
lean_dec(v_r_72_);
lean_dec_ref(v_00_u03c3_71_);
lean_dec_ref(v_Xo_69_);
lean_dec_ref(v_l_68_);
lean_dec_ref(v_Dw_67_);
lean_dec_ref(v_H_66_);
lean_dec_ref(v_inst_63_);
return v_res_74_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_L2DefiniteCuspForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_NonnegIffOfLiesTotal(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ValSetAlgSubset(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PtFree(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FreeBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_L2DefiniteCuspForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_NonnegIffOfLiesTotal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ValSetAlgSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PtFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
