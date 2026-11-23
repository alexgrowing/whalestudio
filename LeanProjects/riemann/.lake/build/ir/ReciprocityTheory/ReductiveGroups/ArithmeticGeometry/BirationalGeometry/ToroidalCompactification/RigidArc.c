// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
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
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v_D_u2080_2_; lean_object* v_mod_3_; lean_object* v_oa_4_; lean_object* v_be_5_; lean_object* v_eta_6_; lean_object* v_etaA_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_14_; 
v_D_u2080_2_ = lean_ctor_get(v_a_1_, 0);
v_mod_3_ = lean_ctor_get(v_a_1_, 1);
v_oa_4_ = lean_ctor_get(v_a_1_, 2);
v_be_5_ = lean_ctor_get(v_a_1_, 3);
v_eta_6_ = lean_ctor_get(v_a_1_, 4);
v_etaA_7_ = lean_ctor_get(v_a_1_, 5);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_14_ == 0)
{
v___x_9_ = v_a_1_;
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_etaA_7_);
lean_inc(v_eta_6_);
lean_inc(v_be_5_);
lean_inc(v_oa_4_);
lean_inc(v_mod_3_);
lean_inc(v_D_u2080_2_);
lean_dec(v_a_1_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
if (v_isShared_10_ == 0)
{
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_D_u2080_2_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_mod_3_);
lean_ctor_set(v_reuseFailAlloc_13_, 2, v_oa_4_);
lean_ctor_set(v_reuseFailAlloc_13_, 3, v_be_5_);
lean_ctor_set(v_reuseFailAlloc_13_, 4, v_eta_6_);
lean_ctor_set(v_reuseFailAlloc_13_, 5, v_etaA_7_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_H_19_, lean_object* v_D_20_, lean_object* v_l_21_, lean_object* v_c_22_, lean_object* v_k_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_bF_26_, lean_object* v_a_27_, lean_object* v_O_28_, lean_object* v_inst_29_, lean_object* v_00_u03b2_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict___redArg(v_a_27_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict___boxed(lean_object* v_E_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_H_36_, lean_object* v_D_37_, lean_object* v_l_38_, lean_object* v_c_39_, lean_object* v_k_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_bF_43_, lean_object* v_a_44_, lean_object* v_O_45_, lean_object* v_inst_46_, lean_object* v_00_u03b2_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcIn_restrict(v_E_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_H_36_, v_D_37_, v_l_38_, v_c_39_, v_k_40_, v_inst_41_, v_inst_42_, v_bF_43_, v_a_44_, v_O_45_, v_inst_46_, v_00_u03b2_47_);
lean_dec_ref(v_00_u03b2_47_);
lean_dec_ref(v_inst_46_);
lean_dec(v_bF_43_);
lean_dec_ref(v_inst_41_);
lean_dec_ref(v_l_38_);
lean_dec_ref(v_D_37_);
lean_dec_ref(v_H_36_);
lean_dec_ref(v_inst_33_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
