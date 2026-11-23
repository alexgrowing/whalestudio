// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
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
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_pullU___redArg(lean_object*, lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0(lean_object* v_00_u03c8_3_, lean_object* v_L_4_, lean_object* v_j_5_, lean_object* v_j_x27_6_, lean_object* v_Y_7_, lean_object* v___x_8_, lean_object* v_00_u03b5_9_, lean_object* v_toMonoid_10_, lean_object* v_k_11_){
_start:
{
lean_object* v___x_12_; lean_object* v_g_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_356__overap_18_; lean_object* v___x_19_; lean_object* v___x_357__overap_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_intZero_23_; uint8_t v_isNeg_24_; 
lean_inc_n(v_k_11_, 3);
v___x_12_ = lean_apply_1(v_00_u03c8_3_, v_k_11_);
v_g_13_ = lean_ctor_get(v_L_4_, 1);
lean_inc_ref(v_g_13_);
lean_dec_ref(v_L_4_);
v___x_14_ = lean_apply_1(v_j_5_, v_k_11_);
v___x_15_ = lean_apply_1(v_j_x27_6_, v_k_11_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_apply_2(v_g_13_, v___x_14_, v___x_15_);
v___x_356__overap_18_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_pullU___redArg(v___x_12_, v___x_16_);
v___x_19_ = lean_apply_1(v___x_356__overap_18_, v___x_17_);
v___x_357__overap_20_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(v_Y_7_, v___x_8_, v___x_8_);
v___x_21_ = lean_apply_1(v___x_357__overap_20_, v___x_19_);
v___x_22_ = lean_apply_1(v_00_u03b5_9_, v_k_11_);
v_intZero_23_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0___closed__0);
v_isNeg_24_ = lean_int_dec_lt(v___x_22_, v_intZero_23_);
if (v_isNeg_24_ == 0)
{
lean_object* v_toNPow_25_; lean_object* v_val_26_; lean_object* v_inv_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_37_; 
v_toNPow_25_ = lean_ctor_get(v_toMonoid_10_, 2);
lean_inc(v_toNPow_25_);
lean_dec_ref(v_toMonoid_10_);
v_val_26_ = lean_ctor_get(v___x_21_, 0);
v_inv_27_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_37_ == 0)
{
v___x_29_ = v___x_21_;
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_inv_27_);
lean_inc(v_val_26_);
lean_dec(v___x_21_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v_a_31_ = lean_nat_abs(v___x_22_);
lean_dec(v___x_22_);
lean_inc(v_toNPow_25_);
lean_inc(v_a_31_);
v___x_32_ = lean_apply_2(v_toNPow_25_, v_a_31_, v_val_26_);
v___x_33_ = lean_apply_2(v_toNPow_25_, v_a_31_, v_inv_27_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___x_33_);
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_35_ = v___x_29_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_toNPow_38_; lean_object* v_val_39_; lean_object* v_inv_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_53_; 
v_toNPow_38_ = lean_ctor_get(v_toMonoid_10_, 2);
lean_inc(v_toNPow_38_);
lean_dec_ref(v_toMonoid_10_);
v_val_39_ = lean_ctor_get(v___x_21_, 0);
v_inv_40_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_53_ == 0)
{
v___x_42_ = v___x_21_;
v_isShared_43_ = v_isSharedCheck_53_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_inv_40_);
lean_inc(v_val_39_);
lean_dec(v___x_21_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_53_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_abs_44_; lean_object* v_one_45_; lean_object* v_a_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v_abs_44_ = lean_nat_abs(v___x_22_);
lean_dec(v___x_22_);
v_one_45_ = lean_unsigned_to_nat(1u);
v_a_46_ = lean_nat_sub(v_abs_44_, v_one_45_);
lean_dec(v_abs_44_);
v___x_47_ = lean_nat_add(v_a_46_, v_one_45_);
lean_dec(v_a_46_);
lean_inc(v_toNPow_38_);
lean_inc(v___x_47_);
v___x_48_ = lean_apply_2(v_toNPow_38_, v___x_47_, v_val_39_);
v___x_49_ = lean_apply_2(v_toNPow_38_, v___x_47_, v_inv_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_48_);
lean_ctor_set(v___x_42_, 0, v___x_49_);
v___x_51_ = v___x_42_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_48_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg(lean_object* v_Y_54_, lean_object* v_L_55_, lean_object* v_inst_56_, lean_object* v_00_u03c8_57_, lean_object* v_00_u03b5_58_, lean_object* v_j_59_, lean_object* v_j_x27_60_){
_start:
{
lean_object* v_presheaf_61_; lean_object* v_obj_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_toSemiring_67_; lean_object* v_toMonoid_68_; lean_object* v_toMonoid_69_; lean_object* v___f_70_; lean_object* v___x_71_; 
v_presheaf_61_ = lean_ctor_get(v_Y_54_, 1);
v_obj_62_ = lean_ctor_get(v_presheaf_61_, 0);
v___x_63_ = lean_box(0);
lean_inc(v_obj_62_);
v___x_64_ = lean_apply_1(v_obj_62_, v___x_63_);
v___x_65_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_64_);
v___x_66_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_65_);
v_toSemiring_67_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_toSemiring_67_);
lean_dec_ref(v___x_64_);
v_toMonoid_68_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_toMonoid_68_);
lean_dec_ref(v___x_66_);
v_toMonoid_69_ = lean_ctor_get(v_toSemiring_67_, 1);
lean_inc_ref(v_toMonoid_69_);
lean_dec_ref(v_toSemiring_67_);
v___f_70_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg___lam__0), 9, 8);
lean_closure_set(v___f_70_, 0, v_00_u03c8_57_);
lean_closure_set(v___f_70_, 1, v_L_55_);
lean_closure_set(v___f_70_, 2, v_j_59_);
lean_closure_set(v___f_70_, 3, v_j_x27_60_);
lean_closure_set(v___f_70_, 4, v_Y_54_);
lean_closure_set(v___f_70_, 5, v___x_63_);
lean_closure_set(v___f_70_, 6, v_00_u03b5_58_);
lean_closure_set(v___f_70_, 7, v_toMonoid_69_);
v___x_71_ = lp_mathlib_Finset_prod___redArg(v_toMonoid_68_, v_inst_56_, v___f_70_);
lean_dec_ref(v_toMonoid_68_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw(lean_object* v_X_72_, lean_object* v_Y_73_, lean_object* v_L_74_, lean_object* v_K_75_, lean_object* v_inst_76_, lean_object* v_00_u03c8_77_, lean_object* v_00_u03b5_78_, lean_object* v_j_79_, lean_object* v_j_x27_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___redArg(v_Y_73_, v_L_74_, v_inst_76_, v_00_u03c8_77_, v_00_u03b5_78_, v_j_79_, v_j_x27_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw___boxed(lean_object* v_X_82_, lean_object* v_Y_83_, lean_object* v_L_84_, lean_object* v_K_85_, lean_object* v_inst_86_, lean_object* v_00_u03c8_87_, lean_object* v_00_u03b5_88_, lean_object* v_j_89_, lean_object* v_j_x27_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_gw(v_X_82_, v_Y_83_, v_L_84_, v_K_85_, v_inst_86_, v_00_u03c8_87_, v_00_u03b5_88_, v_j_89_, v_j_x27_90_);
lean_dec_ref(v_X_82_);
return v_res_91_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
