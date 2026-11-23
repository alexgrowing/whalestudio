// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
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
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_div(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_pullU___redArg(lean_object*, lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0(lean_object* v_p_3_, lean_object* v_obj_4_, lean_object* v_X_5_, lean_object* v_M_6_, lean_object* v_L_7_, lean_object* v_00_u03c6_8_, lean_object* v_w_9_, lean_object* v_Y_10_, lean_object* v_00_u03b5_11_, lean_object* v_k_12_){
_start:
{
lean_object* v_fst_13_; lean_object* v_snd_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_68_; 
v_fst_13_ = lean_ctor_get(v_p_3_, 0);
v_snd_14_ = lean_ctor_get(v_p_3_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_p_3_);
if (v_isSharedCheck_68_ == 0)
{
v___x_16_ = v_p_3_;
v_isShared_17_ = v_isSharedCheck_68_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_snd_14_);
lean_inc(v_fst_13_);
lean_dec(v_p_3_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_68_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toSemiring_20_; lean_object* v_toMonoid_21_; lean_object* v___x_22_; lean_object* v_U_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_obj_4_, v___x_18_);
v_toSemiring_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_toSemiring_20_);
lean_dec_ref(v___x_19_);
v_toMonoid_21_ = lean_ctor_get(v_toSemiring_20_, 1);
lean_inc_ref(v_toMonoid_21_);
lean_dec_ref(v_toSemiring_20_);
v___x_22_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_div(v_X_5_, v_M_6_, v_L_7_);
v_U_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_U_23_);
lean_dec_ref(v___x_22_);
lean_inc_n(v_k_12_, 3);
v___x_24_ = lean_apply_1(v_00_u03c6_8_, v_k_12_);
v___x_25_ = lean_apply_1(v_fst_13_, v_k_12_);
v___x_26_ = lean_apply_1(v_snd_14_, v_k_12_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 1, v___x_26_);
lean_ctor_set(v___x_16_, 0, v___x_25_);
v___x_28_ = v___x_16_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_26_);
v___x_28_ = v_reuseFailAlloc_67_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_326__overap_31_; lean_object* v___x_32_; lean_object* v___x_327__overap_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_intZero_36_; uint8_t v_isNeg_37_; 
lean_inc_ref(v___x_28_);
v___x_29_ = lean_apply_1(v_U_23_, v___x_28_);
v___x_30_ = lean_apply_1(v_w_9_, v___x_28_);
v___x_326__overap_31_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_pullU___redArg(v___x_24_, v___x_29_);
v___x_32_ = lean_apply_1(v___x_326__overap_31_, v___x_30_);
v___x_327__overap_33_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(v_Y_10_, v___x_18_, v___x_18_);
v___x_34_ = lean_apply_1(v___x_327__overap_33_, v___x_32_);
v___x_35_ = lean_apply_1(v_00_u03b5_11_, v_k_12_);
v_intZero_36_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0___closed__0);
v_isNeg_37_ = lean_int_dec_lt(v___x_35_, v_intZero_36_);
if (v_isNeg_37_ == 0)
{
lean_object* v_toNPow_38_; lean_object* v_val_39_; lean_object* v_inv_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_50_; 
v_toNPow_38_ = lean_ctor_get(v_toMonoid_21_, 2);
lean_inc(v_toNPow_38_);
lean_dec_ref(v_toMonoid_21_);
v_val_39_ = lean_ctor_get(v___x_34_, 0);
v_inv_40_ = lean_ctor_get(v___x_34_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_50_ == 0)
{
v___x_42_ = v___x_34_;
v_isShared_43_ = v_isSharedCheck_50_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_inv_40_);
lean_inc(v_val_39_);
lean_dec(v___x_34_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_50_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_a_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v_a_44_ = lean_nat_abs(v___x_35_);
lean_dec(v___x_35_);
lean_inc(v_toNPow_38_);
lean_inc(v_a_44_);
v___x_45_ = lean_apply_2(v_toNPow_38_, v_a_44_, v_val_39_);
v___x_46_ = lean_apply_2(v_toNPow_38_, v_a_44_, v_inv_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_46_);
lean_ctor_set(v___x_42_, 0, v___x_45_);
v___x_48_ = v___x_42_;
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
else
{
lean_object* v_toNPow_51_; lean_object* v_val_52_; lean_object* v_inv_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_66_; 
v_toNPow_51_ = lean_ctor_get(v_toMonoid_21_, 2);
lean_inc(v_toNPow_51_);
lean_dec_ref(v_toMonoid_21_);
v_val_52_ = lean_ctor_get(v___x_34_, 0);
v_inv_53_ = lean_ctor_get(v___x_34_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_66_ == 0)
{
v___x_55_ = v___x_34_;
v_isShared_56_ = v_isSharedCheck_66_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_inv_53_);
lean_inc(v_val_52_);
lean_dec(v___x_34_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_66_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_abs_57_; lean_object* v_one_58_; lean_object* v_a_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v_abs_57_ = lean_nat_abs(v___x_35_);
lean_dec(v___x_35_);
v_one_58_ = lean_unsigned_to_nat(1u);
v_a_59_ = lean_nat_sub(v_abs_57_, v_one_58_);
lean_dec(v_abs_57_);
v___x_60_ = lean_nat_add(v_a_59_, v_one_58_);
lean_dec(v_a_59_);
lean_inc(v_toNPow_51_);
lean_inc(v___x_60_);
v___x_61_ = lean_apply_2(v_toNPow_51_, v___x_60_, v_val_52_);
v___x_62_ = lean_apply_2(v_toNPow_51_, v___x_60_, v_inv_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_61_);
lean_ctor_set(v___x_55_, 0, v___x_62_);
v___x_64_ = v___x_55_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_61_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__1(lean_object* v_Y_69_, lean_object* v___x_70_, lean_object* v_X_71_, lean_object* v_M_72_, lean_object* v_L_73_, lean_object* v_00_u03c6_74_, lean_object* v_w_75_, lean_object* v_00_u03b5_76_, lean_object* v_inst_77_, lean_object* v_p_78_){
_start:
{
lean_object* v_presheaf_79_; lean_object* v_obj_80_; lean_object* v_U_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_toMonoid_86_; lean_object* v___f_87_; lean_object* v___x_88_; 
v_presheaf_79_ = lean_ctor_get(v_Y_69_, 1);
v_obj_80_ = lean_ctor_get(v_presheaf_79_, 0);
lean_inc_n(v_obj_80_, 2);
v_U_81_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_U_81_);
lean_dec_ref(v___x_70_);
lean_inc_ref(v_p_78_);
v___x_82_ = lean_apply_1(v_U_81_, v_p_78_);
v___x_83_ = lean_apply_1(v_obj_80_, v___x_82_);
v___x_84_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_83_);
lean_dec_ref(v___x_83_);
v___x_85_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_84_);
v_toMonoid_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_toMonoid_86_);
lean_dec_ref(v___x_85_);
v___f_87_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__0), 10, 9);
lean_closure_set(v___f_87_, 0, v_p_78_);
lean_closure_set(v___f_87_, 1, v_obj_80_);
lean_closure_set(v___f_87_, 2, v_X_71_);
lean_closure_set(v___f_87_, 3, v_M_72_);
lean_closure_set(v___f_87_, 4, v_L_73_);
lean_closure_set(v___f_87_, 5, v_00_u03c6_74_);
lean_closure_set(v___f_87_, 6, v_w_75_);
lean_closure_set(v___f_87_, 7, v_Y_69_);
lean_closure_set(v___f_87_, 8, v_00_u03b5_76_);
v___x_88_ = lp_mathlib_Finset_prod___redArg(v_toMonoid_86_, v_inst_77_, v___f_87_);
lean_dec_ref(v_toMonoid_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg(lean_object* v_X_89_, lean_object* v_Y_90_, lean_object* v_L_91_, lean_object* v_M_92_, lean_object* v_inst_93_, lean_object* v_w_94_, lean_object* v_00_u03c6_95_, lean_object* v_00_u03b5_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___f_100_; 
lean_inc_ref_n(v_00_u03b5_96_, 2);
lean_inc_ref_n(v_00_u03c6_95_, 2);
lean_inc_n(v_inst_93_, 2);
lean_inc_ref(v_M_92_);
lean_inc_ref_n(v_Y_90_, 3);
lean_inc_ref_n(v_X_89_, 2);
v___x_97_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_X_89_, v_Y_90_, v_M_92_, v_inst_93_, v_00_u03c6_95_, v_00_u03b5_96_);
lean_inc_ref(v_L_91_);
v___x_98_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_X_89_, v_Y_90_, v_L_91_, v_inst_93_, v_00_u03c6_95_, v_00_u03b5_96_);
v___x_99_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_div(v_Y_90_, v___x_97_, v___x_98_);
v___f_100_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg___lam__1), 10, 9);
lean_closure_set(v___f_100_, 0, v_Y_90_);
lean_closure_set(v___f_100_, 1, v___x_99_);
lean_closure_set(v___f_100_, 2, v_X_89_);
lean_closure_set(v___f_100_, 3, v_M_92_);
lean_closure_set(v___f_100_, 4, v_L_91_);
lean_closure_set(v___f_100_, 5, v_00_u03c6_95_);
lean_closure_set(v___f_100_, 6, v_w_94_);
lean_closure_set(v___f_100_, 7, v_00_u03b5_96_);
lean_closure_set(v___f_100_, 8, v_inst_93_);
return v___f_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso(lean_object* v_X_101_, lean_object* v_Y_102_, lean_object* v_L_103_, lean_object* v_M_104_, lean_object* v_K_105_, lean_object* v_inst_106_, lean_object* v_w_107_, lean_object* v_00_u03c6_108_, lean_object* v_00_u03b5_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_linCombIso___redArg(v_X_101_, v_Y_102_, v_L_103_, v_M_104_, v_inst_106_, v_w_107_, v_00_u03c6_108_, v_00_u03b5_109_);
return v___x_110_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
