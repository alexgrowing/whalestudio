// Lean compiler output
// Module: Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_geoC___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_geoC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_geoC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC___redArg(lean_object* v_G_1_, lean_object* v_A_2_, lean_object* v_L_3_, lean_object* v_c_4_){
_start:
{
lean_object* v_arTop_5_; lean_object* v_Yv_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_arTop_5_ = lean_ctor_get(v_G_1_, 22);
lean_inc(v_arTop_5_);
lean_dec_ref(v_G_1_);
v_Yv_6_ = lean_ctor_get(v_A_2_, 0);
lean_inc(v_Yv_6_);
lean_dec_ref(v_A_2_);
lean_inc(v_c_4_);
v___x_7_ = lean_apply_1(v_Yv_6_, v_c_4_);
v___x_8_ = lean_apply_1(v_L_3_, v_c_4_);
v___x_9_ = lean_apply_2(v_arTop_5_, v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC(lean_object* v_D_10_, lean_object* v_G_11_, lean_object* v_Tau_12_, lean_object* v_inst_13_, lean_object* v_N_14_, lean_object* v_Comp_15_, lean_object* v_inst_16_, lean_object* v_A_17_, lean_object* v_L_18_, lean_object* v_c_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC___redArg(v_G_11_, v_A_17_, v_L_18_, v_c_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC___boxed(lean_object* v_D_21_, lean_object* v_G_22_, lean_object* v_Tau_23_, lean_object* v_inst_24_, lean_object* v_N_25_, lean_object* v_Comp_26_, lean_object* v_inst_27_, lean_object* v_A_28_, lean_object* v_L_29_, lean_object* v_c_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_Geo_AlgPkg_arSelfC(v_D_21_, v_G_22_, v_Tau_23_, v_inst_24_, v_N_25_, v_Comp_26_, v_inst_27_, v_A_28_, v_L_29_, v_c_30_);
lean_dec(v_inst_27_);
lean_dec(v_N_25_);
lean_dec(v_inst_24_);
lean_dec_ref(v_D_21_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_geoC___redArg(lean_object* v_A_32_, lean_object* v_L_33_, lean_object* v_c_34_){
_start:
{
lean_object* v_degA_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_degA_35_ = lean_ctor_get(v_A_32_, 4);
lean_inc(v_degA_35_);
lean_dec_ref(v_A_32_);
lean_inc(v_c_34_);
v___x_36_ = lean_apply_1(v_L_33_, v_c_34_);
v___x_37_ = lean_apply_2(v_degA_35_, v_c_34_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_geoC(lean_object* v_D_38_, lean_object* v_G_39_, lean_object* v_Tau_40_, lean_object* v_inst_41_, lean_object* v_N_42_, lean_object* v_Comp_43_, lean_object* v_inst_44_, lean_object* v_A_45_, lean_object* v_L_46_, lean_object* v_c_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_L2_Geo_AlgPkg_geoC___redArg(v_A_45_, v_L_46_, v_c_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_geoC___boxed(lean_object* v_D_49_, lean_object* v_G_50_, lean_object* v_Tau_51_, lean_object* v_inst_52_, lean_object* v_N_53_, lean_object* v_Comp_54_, lean_object* v_inst_55_, lean_object* v_A_56_, lean_object* v_L_57_, lean_object* v_c_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_L2_Geo_AlgPkg_geoC(v_D_49_, v_G_50_, v_Tau_51_, v_inst_52_, v_N_53_, v_Comp_54_, v_inst_55_, v_A_56_, v_L_57_, v_c_58_);
lean_dec(v_inst_55_);
lean_dec(v_N_53_);
lean_dec(v_inst_52_);
lean_dec_ref(v_G_50_);
lean_dec_ref(v_D_49_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol___redArg___lam__0(lean_object* v_G_60_, lean_object* v_A_61_, lean_object* v_L_62_, lean_object* v_c_63_){
_start:
{
lean_object* v_arVol_64_; lean_object* v_Yv_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_arVol_64_ = lean_ctor_get(v_G_60_, 23);
lean_inc(v_arVol_64_);
lean_dec_ref(v_G_60_);
v_Yv_65_ = lean_ctor_get(v_A_61_, 0);
lean_inc(v_Yv_65_);
lean_dec_ref(v_A_61_);
lean_inc(v_c_63_);
v___x_66_ = lean_apply_1(v_Yv_65_, v_c_63_);
v___x_67_ = lean_apply_1(v_L_62_, v_c_63_);
v___x_68_ = lean_apply_2(v_arVol_64_, v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol___redArg(lean_object* v_G_69_, lean_object* v_inst_70_, lean_object* v_A_71_, lean_object* v_L_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___f_73_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_AlgPkg_arVol___redArg___lam__0), 4, 3);
lean_closure_set(v___f_73_, 0, v_G_69_);
lean_closure_set(v___f_73_, 1, v_A_71_);
lean_closure_set(v___f_73_, 2, v_L_72_);
v___x_74_ = lp_mathlib_Real_instAddCommMonoid;
v___x_75_ = lp_mathlib_Finset_sum___redArg(v___x_74_, v_inst_70_, v___f_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol(lean_object* v_D_76_, lean_object* v_G_77_, lean_object* v_Tau_78_, lean_object* v_inst_79_, lean_object* v_N_80_, lean_object* v_Comp_81_, lean_object* v_inst_82_, lean_object* v_A_83_, lean_object* v_L_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_tree_Formalism_L2_Geo_AlgPkg_arVol___redArg(v_G_77_, v_inst_82_, v_A_83_, v_L_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_AlgPkg_arVol___boxed(lean_object* v_D_86_, lean_object* v_G_87_, lean_object* v_Tau_88_, lean_object* v_inst_89_, lean_object* v_N_90_, lean_object* v_Comp_91_, lean_object* v_inst_92_, lean_object* v_A_93_, lean_object* v_L_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_tree_Formalism_L2_Geo_AlgPkg_arVol(v_D_86_, v_G_87_, v_Tau_88_, v_inst_89_, v_N_90_, v_Comp_91_, v_inst_92_, v_A_93_, v_L_94_);
lean_dec(v_N_90_);
lean_dec(v_inst_89_);
lean_dec_ref(v_D_86_);
return v_res_95_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_ArVolEqOfNef(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
