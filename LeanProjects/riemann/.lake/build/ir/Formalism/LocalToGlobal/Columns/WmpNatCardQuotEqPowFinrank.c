// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.WmpNatCardQuotEqPowFinrank
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.WmLemmas public import Formalism.FlagUnipotentLattices.IdealCountLeWAsm public import Lemmata.GeneralBFactRightMore.Imports
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
lean_object* lp_tree_Formalism_L2_Col_restr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpToK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpToK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpkTop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpkTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpkTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpC(lean_object* v_E_1_, lean_object* v_inst_2_, lean_object* v_n_3_, lean_object* v_P_4_, lean_object* v_a_5_, lean_object* v_N_6_, lean_object* v_N_u2081_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpC___boxed(lean_object* v_E_9_, lean_object* v_inst_10_, lean_object* v_n_11_, lean_object* v_P_12_, lean_object* v_a_13_, lean_object* v_N_14_, lean_object* v_N_u2081_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_L2_Col_wmpC(v_E_9_, v_inst_10_, v_n_11_, v_P_12_, v_a_13_, v_N_14_, v_N_u2081_15_);
lean_dec(v_a_13_);
lean_dec(v_n_11_);
lean_dec_ref(v_inst_10_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpToK(lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_P_19_, lean_object* v_V_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_p_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpToK___boxed(lean_object* v_E_27_, lean_object* v_inst_28_, lean_object* v_P_29_, lean_object* v_V_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_p_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_L2_Col_wmpToK(v_E_27_, v_inst_28_, v_P_29_, v_V_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_p_35_);
lean_dec(v_inst_33_);
lean_dec(v_inst_32_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_28_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpkTop___redArg(lean_object* v_r_37_, lean_object* v_n_38_, lean_object* v_g_39_){
_start:
{
lean_object* v_val_40_; lean_object* v_inv_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_50_; 
v_val_40_ = lean_ctor_get(v_g_39_, 0);
v_inv_41_ = lean_ctor_get(v_g_39_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_g_39_);
if (v_isSharedCheck_50_ == 0)
{
v___x_43_ = v_g_39_;
v_isShared_44_ = v_isSharedCheck_50_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_inv_41_);
lean_inc(v_val_40_);
lean_dec(v_g_39_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_50_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
lean_inc(v_r_37_);
lean_inc(v_n_38_);
v___x_45_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_restr___boxed), 7, 5);
lean_closure_set(v___x_45_, 0, v_n_38_);
lean_closure_set(v___x_45_, 1, lean_box(0));
lean_closure_set(v___x_45_, 2, v_r_37_);
lean_closure_set(v___x_45_, 3, lean_box(0));
lean_closure_set(v___x_45_, 4, v_val_40_);
v___x_46_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_restr___boxed), 7, 5);
lean_closure_set(v___x_46_, 0, v_n_38_);
lean_closure_set(v___x_46_, 1, lean_box(0));
lean_closure_set(v___x_46_, 2, v_r_37_);
lean_closure_set(v___x_46_, 3, lean_box(0));
lean_closure_set(v___x_46_, 4, v_inv_41_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v___x_46_);
lean_ctor_set(v___x_43_, 0, v___x_45_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpkTop(lean_object* v_00_u03ba_51_, lean_object* v_inst_52_, lean_object* v_r_53_, lean_object* v_n_54_, lean_object* v_h_55_, lean_object* v_bl_56_, lean_object* v_g_57_, lean_object* v_hg_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_L2_Col_wmpkTop___redArg(v_r_53_, v_n_54_, v_g_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmpkTop___boxed(lean_object* v_00_u03ba_60_, lean_object* v_inst_61_, lean_object* v_r_62_, lean_object* v_n_63_, lean_object* v_h_64_, lean_object* v_bl_65_, lean_object* v_g_66_, lean_object* v_hg_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Formalism_L2_Col_wmpkTop(v_00_u03ba_60_, v_inst_61_, v_r_62_, v_n_63_, v_h_64_, v_bl_65_, v_g_66_, v_hg_67_);
lean_dec(v_bl_65_);
lean_dec_ref(v_inst_61_);
return v_res_68_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_WmLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_FlagUnipotentLattices_IdealCountLeWAsm(uint8_t builtin);
lean_object* initialize_tree_Lemmata_GeneralBFactRightMore_Imports(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_WmpNatCardQuotEqPowFinrank(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_WmLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FlagUnipotentLattices_IdealCountLeWAsm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_GeneralBFactRightMore_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
