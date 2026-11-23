// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData public import Formalism.LocalToGlobal.LatticeGeometry.ViewsC public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill___redArg(lean_object* v_G_u2080_1_, lean_object* v_del_2_, lean_object* v_th_x27_3_, lean_object* v_rz_4_, lean_object* v_alz_5_, lean_object* v_th0_6_, lean_object* v_zc_7_, lean_object* v_rq_8_, lean_object* v_th_9_, lean_object* v_iet_10_, lean_object* v_et_11_){
_start:
{
lean_object* v_N_12_; lean_object* v_w_13_; lean_object* v_mx_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_N_12_ = lean_ctor_get(v_G_u2080_1_, 0);
v_w_13_ = lean_ctor_get(v_G_u2080_1_, 1);
v_mx_14_ = lean_ctor_get(v_G_u2080_1_, 12);
v_isSharedCheck_21_ = !lean_is_exclusive(v_G_u2080_1_);
if (v_isSharedCheck_21_ == 0)
{
lean_object* v_unused_22_; lean_object* v_unused_23_; lean_object* v_unused_24_; lean_object* v_unused_25_; lean_object* v_unused_26_; lean_object* v_unused_27_; lean_object* v_unused_28_; lean_object* v_unused_29_; lean_object* v_unused_30_; lean_object* v_unused_31_; 
v_unused_22_ = lean_ctor_get(v_G_u2080_1_, 11);
lean_dec(v_unused_22_);
v_unused_23_ = lean_ctor_get(v_G_u2080_1_, 10);
lean_dec(v_unused_23_);
v_unused_24_ = lean_ctor_get(v_G_u2080_1_, 9);
lean_dec(v_unused_24_);
v_unused_25_ = lean_ctor_get(v_G_u2080_1_, 8);
lean_dec(v_unused_25_);
v_unused_26_ = lean_ctor_get(v_G_u2080_1_, 7);
lean_dec(v_unused_26_);
v_unused_27_ = lean_ctor_get(v_G_u2080_1_, 6);
lean_dec(v_unused_27_);
v_unused_28_ = lean_ctor_get(v_G_u2080_1_, 5);
lean_dec(v_unused_28_);
v_unused_29_ = lean_ctor_get(v_G_u2080_1_, 4);
lean_dec(v_unused_29_);
v_unused_30_ = lean_ctor_get(v_G_u2080_1_, 3);
lean_dec(v_unused_30_);
v_unused_31_ = lean_ctor_get(v_G_u2080_1_, 2);
lean_dec(v_unused_31_);
v___x_16_ = v_G_u2080_1_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_mx_14_);
lean_inc(v_w_13_);
lean_inc(v_N_12_);
lean_dec(v_G_u2080_1_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 11, v_et_11_);
lean_ctor_set(v___x_16_, 10, v_iet_10_);
lean_ctor_set(v___x_16_, 9, v_th_9_);
lean_ctor_set(v___x_16_, 8, v_rq_8_);
lean_ctor_set(v___x_16_, 7, v_zc_7_);
lean_ctor_set(v___x_16_, 6, v_th0_6_);
lean_ctor_set(v___x_16_, 5, v_alz_5_);
lean_ctor_set(v___x_16_, 4, v_rz_4_);
lean_ctor_set(v___x_16_, 3, v_th_x27_3_);
lean_ctor_set(v___x_16_, 2, v_del_2_);
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_N_12_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_w_13_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_del_2_);
lean_ctor_set(v_reuseFailAlloc_20_, 3, v_th_x27_3_);
lean_ctor_set(v_reuseFailAlloc_20_, 4, v_rz_4_);
lean_ctor_set(v_reuseFailAlloc_20_, 5, v_alz_5_);
lean_ctor_set(v_reuseFailAlloc_20_, 6, v_th0_6_);
lean_ctor_set(v_reuseFailAlloc_20_, 7, v_zc_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 8, v_rq_8_);
lean_ctor_set(v_reuseFailAlloc_20_, 9, v_th_9_);
lean_ctor_set(v_reuseFailAlloc_20_, 10, v_iet_10_);
lean_ctor_set(v_reuseFailAlloc_20_, 11, v_et_11_);
lean_ctor_set(v_reuseFailAlloc_20_, 12, v_mx_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill(lean_object* v_D_32_, lean_object* v_B_33_, lean_object* v_P_34_, lean_object* v_j_35_, lean_object* v_X_36_, lean_object* v_ka_37_, lean_object* v_wL_38_, lean_object* v_wF_39_, lean_object* v_G_u2080_40_, lean_object* v_del_41_, lean_object* v_th_x27_42_, lean_object* v_rz_43_, lean_object* v_alz_44_, lean_object* v_th0_45_, lean_object* v_zc_46_, lean_object* v_rq_47_, lean_object* v_th_48_, lean_object* v_iet_49_, lean_object* v_et_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill___redArg(v_G_u2080_40_, v_del_41_, v_th_x27_42_, v_rz_43_, v_alz_44_, v_th0_45_, v_zc_46_, v_rq_47_, v_th_48_, v_iet_49_, v_et_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill___boxed(lean_object** _args){
lean_object* v_D_52_ = _args[0];
lean_object* v_B_53_ = _args[1];
lean_object* v_P_54_ = _args[2];
lean_object* v_j_55_ = _args[3];
lean_object* v_X_56_ = _args[4];
lean_object* v_ka_57_ = _args[5];
lean_object* v_wL_58_ = _args[6];
lean_object* v_wF_59_ = _args[7];
lean_object* v_G_u2080_60_ = _args[8];
lean_object* v_del_61_ = _args[9];
lean_object* v_th_x27_62_ = _args[10];
lean_object* v_rz_63_ = _args[11];
lean_object* v_alz_64_ = _args[12];
lean_object* v_th0_65_ = _args[13];
lean_object* v_zc_66_ = _args[14];
lean_object* v_rq_67_ = _args[15];
lean_object* v_th_68_ = _args[16];
lean_object* v_iet_69_ = _args[17];
lean_object* v_et_70_ = _args[18];
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_MainNotions_Gaps_FamilyHypotheses_refill(v_D_52_, v_B_53_, v_P_54_, v_j_55_, v_X_56_, v_ka_57_, v_wL_58_, v_wF_59_, v_G_u2080_60_, v_del_61_, v_th_x27_62_, v_rz_63_, v_alz_64_, v_th0_65_, v_zc_66_, v_rq_67_, v_th_68_, v_iet_69_, v_et_70_);
lean_dec_ref(v_wF_59_);
lean_dec_ref(v_wL_58_);
lean_dec_ref(v_ka_57_);
lean_dec_ref(v_X_56_);
lean_dec(v_j_55_);
lean_dec_ref(v_P_54_);
lean_dec_ref(v_B_53_);
lean_dec_ref(v_D_52_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_WeightedPrimeSumBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_GlobalFamilyData(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_ViewsC(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_OEOsInjective(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_AdmissibleModuleIffLatticeQuotients(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_WeightedPrimeSumBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_GlobalFamilyData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_ViewsC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_OEOsInjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
