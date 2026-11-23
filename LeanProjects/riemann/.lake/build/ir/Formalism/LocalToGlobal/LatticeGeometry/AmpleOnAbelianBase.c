// Lean compiler output
// Module: Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
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
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degDR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degDR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degDR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degHT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degHT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degHT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degDR___redArg(lean_object* v_D_1_, lean_object* v_X_2_, lean_object* v_p_3_, lean_object* v_c_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_ex_6_; lean_object* v___x_7_; lean_object* v_eTau_8_; lean_object* v_degGrD_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v_toFun_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_ex_6_ = lean_ctor_get(v_X_2_, 1);
lean_inc_ref(v_ex_6_);
lean_dec_ref(v_X_2_);
v___x_7_ = lean_apply_1(v_ex_6_, v_p_3_);
v_eTau_8_ = lean_ctor_get(v_D_1_, 5);
lean_inc_ref(v_eTau_8_);
lean_dec_ref(v_D_1_);
v_degGrD_9_ = lean_ctor_get(v___x_7_, 49);
lean_inc_ref(v_degGrD_9_);
lean_dec_ref(v___x_7_);
v_fst_10_ = lean_ctor_get(v_x_5_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v_x_5_, 1);
lean_inc(v_snd_11_);
lean_dec_ref(v_x_5_);
v_toFun_12_ = lean_ctor_get(v_eTau_8_, 0);
lean_inc(v_toFun_12_);
lean_dec_ref(v_eTau_8_);
v___x_13_ = lean_apply_1(v_toFun_12_, v_fst_10_);
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_snd_11_, v___x_14_);
lean_dec(v_snd_11_);
v___x_16_ = lean_apply_3(v_degGrD_9_, v_c_4_, v___x_13_, v___x_15_);
v___x_17_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degDR(lean_object* v_D_18_, lean_object* v_N_19_, lean_object* v_j_20_, lean_object* v_Comp_21_, lean_object* v_jC_22_, lean_object* v_ng_23_, lean_object* v_X_24_, lean_object* v_p_25_, lean_object* v_c_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_L2_Geo_PadPkg_degDR___redArg(v_D_18_, v_X_24_, v_p_25_, v_c_26_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degDR___boxed(lean_object* v_D_29_, lean_object* v_N_30_, lean_object* v_j_31_, lean_object* v_Comp_32_, lean_object* v_jC_33_, lean_object* v_ng_34_, lean_object* v_X_35_, lean_object* v_p_36_, lean_object* v_c_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_L2_Geo_PadPkg_degDR(v_D_29_, v_N_30_, v_j_31_, v_Comp_32_, v_jC_33_, v_ng_34_, v_X_35_, v_p_36_, v_c_37_, v_x_38_);
lean_dec(v_ng_34_);
lean_dec_ref(v_jC_33_);
lean_dec(v_j_31_);
lean_dec(v_N_30_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degHT___redArg(lean_object* v_X_40_, lean_object* v_p_41_, lean_object* v_c_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_degM_44_; lean_object* v_htMdl_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_degM_44_ = lean_ctor_get(v_X_40_, 6);
lean_inc(v_degM_44_);
v_htMdl_45_ = lean_ctor_get(v_X_40_, 7);
lean_inc(v_htMdl_45_);
lean_dec_ref(v_X_40_);
v_fst_46_ = lean_ctor_get(v_c_42_, 0);
lean_inc_n(v_fst_46_, 2);
v_snd_47_ = lean_ctor_get(v_c_42_, 1);
lean_inc(v_snd_47_);
lean_dec_ref(v_c_42_);
lean_inc(v_p_41_);
v___x_48_ = lean_apply_2(v_htMdl_45_, v_p_41_, v_fst_46_);
v___x_49_ = lean_apply_5(v_degM_44_, v_p_41_, v_fst_46_, v___x_48_, v_snd_47_, v_a_43_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degHT(lean_object* v_D_50_, lean_object* v_N_51_, lean_object* v_j_52_, lean_object* v_Comp_53_, lean_object* v_jC_54_, lean_object* v_ng_55_, lean_object* v_X_56_, lean_object* v_p_57_, lean_object* v_c_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_tree_Formalism_L2_Geo_PadPkg_degHT___redArg(v_X_56_, v_p_57_, v_c_58_, v_a_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_PadPkg_degHT___boxed(lean_object* v_D_61_, lean_object* v_N_62_, lean_object* v_j_63_, lean_object* v_Comp_64_, lean_object* v_jC_65_, lean_object* v_ng_66_, lean_object* v_X_67_, lean_object* v_p_68_, lean_object* v_c_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_L2_Geo_PadPkg_degHT(v_D_61_, v_N_62_, v_j_63_, v_Comp_64_, v_jC_65_, v_ng_66_, v_X_67_, v_p_68_, v_c_69_, v_a_70_);
lean_dec(v_ng_66_);
lean_dec_ref(v_jC_65_);
lean_dec(v_j_63_);
lean_dec(v_N_62_);
lean_dec_ref(v_D_61_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_BoundaryLocalData(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_AmpleOnAbelianBase(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_BoundaryLocalData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
