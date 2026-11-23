// Lean compiler output
// Module: Formalism.LocalToGlobal.LatticeGeometry.NormDetInf
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf___redArg(lean_object* v_self_1_){
_start:
{
lean_object* v_fst_2_; 
v_fst_2_ = lean_ctor_get(v_self_1_, 0);
lean_inc(v_fst_2_);
return v_fst_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf___redArg___boxed(lean_object* v_self_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_tree_Formalism_L2_Geo_CxPkg_compOf___redArg(v_self_3_);
lean_dec_ref(v_self_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf(lean_object* v_Tau_5_, lean_object* v_inst_6_, lean_object* v_N_7_, lean_object* v_j_8_, lean_object* v_Comp_9_, lean_object* v_inst_10_, lean_object* v_X_11_, lean_object* v_self_12_){
_start:
{
lean_object* v_fst_13_; 
v_fst_13_ = lean_ctor_get(v_self_12_, 0);
lean_inc(v_fst_13_);
return v_fst_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_compOf___boxed(lean_object* v_Tau_14_, lean_object* v_inst_15_, lean_object* v_N_16_, lean_object* v_j_17_, lean_object* v_Comp_18_, lean_object* v_inst_19_, lean_object* v_X_20_, lean_object* v_self_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_Geo_CxPkg_compOf(v_Tau_14_, v_inst_15_, v_N_16_, v_j_17_, v_Comp_18_, v_inst_19_, v_X_20_, v_self_21_);
lean_dec_ref(v_self_21_);
lean_dec_ref(v_X_20_);
lean_dec(v_inst_19_);
lean_dec(v_j_17_);
lean_dec(v_N_16_);
lean_dec(v_inst_15_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol___redArg___lam__0(lean_object* v_X_23_, lean_object* v_c_24_){
_start:
{
lean_object* v_volC_25_; lean_object* v___x_26_; 
v_volC_25_ = lean_ctor_get(v_X_23_, 1);
lean_inc(v_volC_25_);
lean_dec_ref(v_X_23_);
v___x_26_ = lean_apply_1(v_volC_25_, v_c_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol___redArg(lean_object* v_inst_27_, lean_object* v_X_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_CxPkg_vol___redArg___lam__0), 2, 1);
lean_closure_set(v___f_29_, 0, v_X_28_);
v___x_30_ = lp_mathlib_Real_instAddCommMonoid;
v___x_31_ = lp_mathlib_Finset_sum___redArg(v___x_30_, v_inst_27_, v___f_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol(lean_object* v_Tau_32_, lean_object* v_inst_33_, lean_object* v_N_34_, lean_object* v_j_35_, lean_object* v_Comp_36_, lean_object* v_inst_37_, lean_object* v_X_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree_Formalism_L2_Geo_CxPkg_vol___redArg(v_inst_37_, v_X_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_CxPkg_vol___boxed(lean_object* v_Tau_40_, lean_object* v_inst_41_, lean_object* v_N_42_, lean_object* v_j_43_, lean_object* v_Comp_44_, lean_object* v_inst_45_, lean_object* v_X_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_L2_Geo_CxPkg_vol(v_Tau_40_, v_inst_41_, v_N_42_, v_j_43_, v_Comp_44_, v_inst_45_, v_X_46_);
lean_dec(v_j_43_);
lean_dec(v_N_42_);
lean_dec(v_inst_41_);
return v_res_47_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_NormDetInf(uint8_t builtin) {
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
