// Lean compiler output
// Module: Lib.DiscreteSeries.Bruhat.FloorGroups
// Imports: public import Init public meta import Init public import Lib.Adelic.Witt.WittTheorem
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
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
extern lean_object* lp_mathlib_PUnit_fintype;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Shape_besselFrame(lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_single___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_mulVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_succ___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_oppositeIndex___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_oppositeIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_oppositeIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorOf(lean_object* v_00_U0001d530_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_val_3_; 
v_val_3_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_3_);
return v_val_3_;
}
else
{
lean_object* v_val_4_; 
v_val_4_ = lean_ctor_get(v_x_2_, 0);
if (lean_obj_tag(v_val_4_) == 0)
{
lean_object* v_val_5_; 
v_val_5_ = lean_ctor_get(v_val_4_, 0);
if (lean_obj_tag(v_val_5_) == 0)
{
lean_object* v_00_u03f1_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_00_u03f1_6_ = lean_ctor_get(v_00_U0001d530_1_, 0);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_00_u03f1_6_, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v_00_u03f1_9_; 
v_00_u03f1_9_ = lean_ctor_get(v_00_U0001d530_1_, 0);
lean_inc(v_00_u03f1_9_);
return v_00_u03f1_9_;
}
}
else
{
lean_object* v_val_10_; 
v_val_10_ = lean_ctor_get(v_val_4_, 0);
lean_inc(v_val_10_);
return v_val_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorOf___boxed(lean_object* v_00_U0001d530_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH_New_Floors_FloorGroups_floorOf(v_00_U0001d530_11_, v_x_12_);
lean_dec_ref(v_x_12_);
lean_dec_ref(v_00_U0001d530_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_oppositeIndex___redArg(lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v_val_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_23_; 
v_val_15_ = lean_ctor_get(v_x_14_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_23_ == 0)
{
v___x_17_ = v_x_14_;
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_val_15_);
lean_dec(v_x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 1);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_val_15_);
v___x_20_ = v_reuseFailAlloc_22_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
else
{
lean_object* v_val_24_; 
v_val_24_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_24_);
if (lean_obj_tag(v_val_24_) == 1)
{
lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_dec_ref_known(v_x_14_, 1);
v_val_25_ = lean_ctor_get(v_val_24_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v_val_24_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v_val_24_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_dec(v_val_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 0);
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_val_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
else
{
lean_dec(v_val_24_);
return v_x_14_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_oppositeIndex(lean_object* v_00_U0001d530_33_, lean_object* v_x_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_GRH_New_Floors_FloorGroups_oppositeIndex___redArg(v_x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_oppositeIndex___boxed(lean_object* v_00_U0001d530_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_Floors_FloorGroups_oppositeIndex(v_00_U0001d530_36_, v_x_37_);
lean_dec_ref(v_00_U0001d530_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter___redArg(lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_, lean_object* v_h__3_42_, lean_object* v_h__4_43_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__4_43_);
lean_dec(v_h__3_42_);
lean_dec(v_h__2_41_);
v_val_44_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v_x_39_, 1);
v___x_45_ = lean_apply_1(v_h__1_40_, v_val_44_);
return v___x_45_;
}
else
{
lean_object* v_val_46_; 
lean_dec(v_h__1_40_);
v_val_46_ = lean_ctor_get(v_x_39_, 0);
if (lean_obj_tag(v_val_46_) == 0)
{
lean_object* v_val_47_; 
lean_dec(v_h__2_41_);
v_val_47_ = lean_ctor_get(v_val_46_, 0);
if (lean_obj_tag(v_val_47_) == 0)
{
lean_object* v_val_48_; lean_object* v___x_49_; 
lean_inc_ref(v_val_47_);
lean_dec_ref_known(v_x_39_, 1);
lean_dec(v_h__4_43_);
v_val_48_ = lean_ctor_get(v_val_47_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v_val_47_, 1);
v___x_49_ = lean_apply_1(v_h__3_42_, v_val_48_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v_h__3_42_);
v___x_50_ = lean_apply_4(v_h__4_43_, v_x_39_, lean_box(0), lean_box(0), lean_box(0));
return v___x_50_;
}
}
else
{
lean_object* v_val_51_; lean_object* v___x_52_; 
lean_inc_ref(v_val_46_);
lean_dec_ref_known(v_x_39_, 1);
lean_dec(v_h__4_43_);
lean_dec(v_h__3_42_);
v_val_51_ = lean_ctor_get(v_val_46_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v_val_46_, 1);
v___x_52_ = lean_apply_1(v_h__2_41_, v_val_51_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter(lean_object* v_00_U0001d530_53_, lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_, lean_object* v_h__4_59_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v_val_60_; lean_object* v___x_61_; 
lean_dec(v_h__4_59_);
lean_dec(v_h__3_58_);
lean_dec(v_h__2_57_);
v_val_60_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v_x_55_, 1);
v___x_61_ = lean_apply_1(v_h__1_56_, v_val_60_);
return v___x_61_;
}
else
{
lean_object* v_val_62_; 
lean_dec(v_h__1_56_);
v_val_62_ = lean_ctor_get(v_x_55_, 0);
if (lean_obj_tag(v_val_62_) == 0)
{
lean_object* v_val_63_; 
lean_dec(v_h__2_57_);
v_val_63_ = lean_ctor_get(v_val_62_, 0);
if (lean_obj_tag(v_val_63_) == 0)
{
lean_object* v_val_64_; lean_object* v___x_65_; 
lean_inc_ref(v_val_63_);
lean_dec_ref_known(v_x_55_, 1);
lean_dec(v_h__4_59_);
v_val_64_ = lean_ctor_get(v_val_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v_val_63_, 1);
v___x_65_ = lean_apply_1(v_h__3_58_, v_val_64_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
lean_dec(v_h__3_58_);
v___x_66_ = lean_apply_4(v_h__4_59_, v_x_55_, lean_box(0), lean_box(0), lean_box(0));
return v___x_66_;
}
}
else
{
lean_object* v_val_67_; lean_object* v___x_68_; 
lean_inc_ref(v_val_62_);
lean_dec_ref_known(v_x_55_, 1);
lean_dec(v_h__4_59_);
lean_dec(v_h__3_58_);
v_val_67_ = lean_ctor_get(v_val_62_, 0);
lean_inc(v_val_67_);
lean_dec_ref_known(v_val_62_, 1);
v___x_68_ = lean_apply_1(v_h__2_57_, v_val_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter___boxed(lean_object* v_00_U0001d530_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_, lean_object* v_h__4_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_floorOf_match__1_splitter(v_00_U0001d530_69_, v_motive_70_, v_x_71_, v_h__1_72_, v_h__2_73_, v_h__3_74_, v_h__4_75_);
lean_dec_ref(v_00_U0001d530_69_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter___redArg(lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_, lean_object* v_h__3_80_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v_val_81_; lean_object* v___x_82_; 
lean_dec(v_h__3_80_);
lean_dec(v_h__2_79_);
v_val_81_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_81_);
lean_dec_ref_known(v_x_77_, 1);
v___x_82_ = lean_apply_1(v_h__1_78_, v_val_81_);
return v___x_82_;
}
else
{
lean_object* v_val_83_; 
lean_dec(v_h__1_78_);
v_val_83_ = lean_ctor_get(v_x_77_, 0);
if (lean_obj_tag(v_val_83_) == 1)
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_inc_ref(v_val_83_);
lean_dec_ref_known(v_x_77_, 1);
lean_dec(v_h__3_80_);
v_val_84_ = lean_ctor_get(v_val_83_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v_val_83_, 1);
v___x_85_ = lean_apply_1(v_h__2_79_, v_val_84_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec(v_h__2_79_);
v___x_86_ = lean_apply_3(v_h__3_80_, v_x_77_, lean_box(0), lean_box(0));
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter(lean_object* v_00_U0001d530_87_, lean_object* v_motive_88_, lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_, lean_object* v_h__3_92_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v_val_93_; lean_object* v___x_94_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
v_val_93_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_val_93_);
lean_dec_ref_known(v_x_89_, 1);
v___x_94_ = lean_apply_1(v_h__1_90_, v_val_93_);
return v___x_94_;
}
else
{
lean_object* v_val_95_; 
lean_dec(v_h__1_90_);
v_val_95_ = lean_ctor_get(v_x_89_, 0);
if (lean_obj_tag(v_val_95_) == 1)
{
lean_object* v_val_96_; lean_object* v___x_97_; 
lean_inc_ref(v_val_95_);
lean_dec_ref_known(v_x_89_, 1);
lean_dec(v_h__3_92_);
v_val_96_ = lean_ctor_get(v_val_95_, 0);
lean_inc(v_val_96_);
lean_dec_ref_known(v_val_95_, 1);
v___x_97_ = lean_apply_1(v_h__2_91_, v_val_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
lean_dec(v_h__2_91_);
v___x_98_ = lean_apply_3(v_h__3_92_, v_x_89_, lean_box(0), lean_box(0));
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter___boxed(lean_object* v_00_U0001d530_99_, lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_, lean_object* v_h__3_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_FloorGroups_0__New_Floors_FloorGroups_oppositeIndex_match__1_splitter(v_00_U0001d530_99_, v_motive_100_, v_x_101_, v_h__1_102_, v_h__2_103_, v_h__3_104_);
lean_dec_ref(v_00_U0001d530_99_);
return v_res_105_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__0(lean_object* v_decEqIndex_106_, lean_object* v_a_107_, lean_object* v_b_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_110_ = l_instDecidableEqSum_decEq___redArg(v_decEqIndex_106_, v___x_109_, v_a_107_, v_b_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__0___boxed(lean_object* v_decEqIndex_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__0(v_decEqIndex_111_, v_a_112_, v_b_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__1(lean_object* v___f_116_, lean_object* v___x_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = l_instDecidableEqSum_decEq___redArg(v___f_116_, v___x_117_, v_a_118_, v_b_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__1___boxed(lean_object* v___f_121_, lean_object* v___x_122_, lean_object* v_a_123_, lean_object* v_b_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__1(v___f_121_, v___x_122_, v_a_123_, v_b_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__2(lean_object* v_00_u03f1_127_, lean_object* v___f_128_, lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___f_132_; uint8_t v___x_133_; 
v___x_131_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_131_, 0, v_00_u03f1_127_);
lean_inc_ref(v___x_131_);
v___f_132_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_132_, 0, v___f_128_);
lean_closure_set(v___f_132_, 1, v___x_131_);
v___x_133_ = l_instDecidableEqSum_decEq___redArg(v___x_131_, v___f_132_, v_a_129_, v_b_130_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__2___boxed(lean_object* v_00_u03f1_134_, lean_object* v___f_135_, lean_object* v_a_136_, lean_object* v_b_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__2(v_00_u03f1_134_, v___f_135_, v_a_136_, v_b_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__3(lean_object* v_toZero_140_, lean_object* v_i_141_){
_start:
{
lean_inc(v_toZero_140_);
return v_toZero_140_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__3___boxed(lean_object* v_toZero_142_, lean_object* v_i_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__3(v_toZero_142_, v_i_143_);
lean_dec_ref(v_i_143_);
lean_dec(v_toZero_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg(lean_object* v_inst_145_, lean_object* v_00_U0001d530_146_, lean_object* v_b_147_, lean_object* v_g_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_00_u03f1_152_; lean_object* v_fintypeIndex_153_; lean_object* v_decEqIndex_154_; lean_object* v_toSemiring_155_; lean_object* v___x_156_; lean_object* v_toZero_157_; lean_object* v___x_158_; lean_object* v_toAddMonoidWithOne_159_; lean_object* v_toOne_160_; lean_object* v_inv_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_150_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_145_);
v___x_151_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_150_);
v_00_u03f1_152_ = lean_ctor_get(v_00_U0001d530_146_, 0);
v_fintypeIndex_153_ = lean_ctor_get(v_00_U0001d530_146_, 1);
v_decEqIndex_154_ = lean_ctor_get(v_00_U0001d530_146_, 2);
v_toSemiring_155_ = lean_ctor_get(v_inst_145_, 0);
lean_inc_ref(v_toSemiring_155_);
v___x_156_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_155_);
v_toZero_157_ = lean_ctor_get(v___x_156_, 1);
lean_inc(v_toZero_157_);
lean_dec_ref(v___x_156_);
v___x_158_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_145_);
v_toAddMonoidWithOne_159_ = lean_ctor_get(v___x_158_, 1);
lean_inc_ref(v_toAddMonoidWithOne_159_);
lean_dec_ref(v___x_158_);
v_toOne_160_ = lean_ctor_get(v_toAddMonoidWithOne_159_, 2);
lean_inc(v_toOne_160_);
lean_dec_ref(v_toAddMonoidWithOne_159_);
v_inv_161_ = lean_ctor_get(v_g_148_, 1);
lean_inc(v_inv_161_);
lean_dec_ref(v_g_148_);
v___x_162_ = lp_mathlib_PUnit_fintype;
lean_inc_n(v_00_u03f1_152_, 2);
v___x_163_ = l_List_finRange(v_00_u03f1_152_);
lean_inc(v_fintypeIndex_153_);
v___x_164_ = lp_mathlib_Multiset_disjSum___redArg(v_fintypeIndex_153_, v___x_162_);
lean_inc(v___x_163_);
v___x_165_ = lp_mathlib_Multiset_disjSum___redArg(v___x_164_, v___x_163_);
lean_inc_ref(v_decEqIndex_154_);
v___f_166_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_166_, 0, v_decEqIndex_154_);
v___f_167_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_167_, 0, v_00_u03f1_152_);
lean_closure_set(v___f_167_, 1, v___f_166_);
v___x_168_ = lp_mathlib_Multiset_disjSum___redArg(v___x_163_, v___x_165_);
v___f_169_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v_toZero_157_);
v___x_170_ = lp_GRH_New_Shape_besselFrame(v_00_U0001d530_146_, v_b_147_);
lean_dec_ref(v_00_U0001d530_146_);
v___x_171_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_171_, 0, lean_box(0));
lean_closure_set(v___x_171_, 1, lean_box(0));
lean_closure_set(v___x_171_, 2, v___f_169_);
lean_closure_set(v___x_171_, 3, v___f_167_);
lean_closure_set(v___x_171_, 4, v___x_170_);
lean_closure_set(v___x_171_, 5, v_toOne_160_);
v___x_172_ = lp_mathlib_Matrix_mulVec___redArg(v___x_151_, v___x_168_, v_inv_161_, v___x_171_, v_a_149_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint(lean_object* v_A_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_00_U0001d530_176_, lean_object* v_T_177_, lean_object* v_b_178_, lean_object* v_g_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lp_GRH_New_Floors_FloorGroups_orbitPoint___redArg(v_inst_174_, v_00_U0001d530_176_, v_b_178_, v_g_179_, v_a_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_orbitPoint___boxed(lean_object* v_A_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_00_U0001d530_185_, lean_object* v_T_186_, lean_object* v_b_187_, lean_object* v_g_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_GRH_New_Floors_FloorGroups_orbitPoint(v_A_182_, v_inst_183_, v_inst_184_, v_00_U0001d530_185_, v_T_186_, v_b_187_, v_g_188_, v_a_189_);
lean_dec(v_T_186_);
lean_dec(v_inst_184_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup___redArg(){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup___redArg___boxed(lean_object* v___dummy_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = lp_GRH_New_Shape_Form_floorGroup___redArg();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup(lean_object* v_A_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_00_U0001d530_198_, lean_object* v_T_199_, lean_object* v_l_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_floorGroup___boxed(lean_object* v_A_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_00_U0001d530_205_, lean_object* v_T_206_, lean_object* v_l_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = lp_GRH_New_Shape_Form_floorGroup(v_A_202_, v_inst_203_, v_inst_204_, v_00_U0001d530_205_, v_T_206_, v_l_207_);
lean_dec(v_l_207_);
lean_dec(v_T_206_);
lean_dec_ref(v_00_U0001d530_205_);
lean_dec(v_inst_204_);
lean_dec_ref(v_inst_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow___redArg(){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow___redArg___boxed(lean_object* v___dummy_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = lp_GRH_New_Shape_Form_unipotentBelow___redArg();
return v_res_212_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow(lean_object* v_A_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_00_U0001d530_216_, lean_object* v_T_217_, lean_object* v_l_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_unipotentBelow___boxed(lean_object* v_A_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_00_U0001d530_223_, lean_object* v_T_224_, lean_object* v_l_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = lp_GRH_New_Shape_Form_unipotentBelow(v_A_220_, v_inst_221_, v_inst_222_, v_00_U0001d530_223_, v_T_224_, v_l_225_);
lean_dec(v_l_225_);
lean_dec(v_T_224_);
lean_dec_ref(v_00_U0001d530_223_);
lean_dec(v_inst_222_);
lean_dec_ref(v_inst_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent___redArg(){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(0);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent___redArg___boxed(lean_object* v___dummy_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = lp_GRH_New_Floors_FloorGroups_floorUnipotent___redArg();
return v_res_230_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent(lean_object* v_A_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_00_U0001d530_234_, lean_object* v_T_235_, lean_object* v_l_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(0);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_FloorGroups_floorUnipotent___boxed(lean_object* v_A_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_00_U0001d530_241_, lean_object* v_T_242_, lean_object* v_l_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = lp_GRH_New_Floors_FloorGroups_floorUnipotent(v_A_238_, v_inst_239_, v_inst_240_, v_00_U0001d530_241_, v_T_242_, v_l_243_);
lean_dec(v_l_243_);
lean_dec(v_T_242_);
lean_dec_ref(v_00_U0001d530_241_);
lean_dec(v_inst_240_);
lean_dec_ref(v_inst_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup___redArg(){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(0);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup___redArg___boxed(lean_object* v___dummy_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_GRH_New_Shape_Form_partialUnitriangularGroup___redArg();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup(lean_object* v_A_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_00_U0001d530_252_, lean_object* v_T_253_, lean_object* v_l_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_box(0);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_partialUnitriangularGroup___boxed(lean_object* v_A_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_00_U0001d530_259_, lean_object* v_T_260_, lean_object* v_l_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = lp_GRH_New_Shape_Form_partialUnitriangularGroup(v_A_256_, v_inst_257_, v_inst_258_, v_00_U0001d530_259_, v_T_260_, v_l_261_);
lean_dec(v_l_261_);
lean_dec(v_T_260_);
lean_dec_ref(v_00_U0001d530_259_);
lean_dec(v_inst_258_);
lean_dec_ref(v_inst_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH___redArg(){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH___redArg___boxed(lean_object* v___dummy_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = lp_GRH_New_Shape_Form_besselH___redArg();
return v_res_266_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH(lean_object* v_R_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_00_U0001d530_270_, lean_object* v_T_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselH___boxed(lean_object* v_R_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_00_U0001d530_276_, lean_object* v_T_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = lp_GRH_New_Shape_Form_besselH(v_R_273_, v_inst_274_, v_inst_275_, v_00_U0001d530_276_, v_T_277_);
lean_dec(v_T_277_);
lean_dec_ref(v_00_U0001d530_276_);
lean_dec(v_inst_275_);
lean_dec_ref(v_inst_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS___redArg(){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS___redArg___boxed(lean_object* v___dummy_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = lp_GRH_New_Shape_Form_besselS___redArg();
return v_res_282_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS(lean_object* v_R_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_00_U0001d530_286_, lean_object* v_T_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Shape_Form_besselS___boxed(lean_object* v_R_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_00_U0001d530_292_, lean_object* v_T_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = lp_GRH_New_Shape_Form_besselS(v_R_289_, v_inst_290_, v_inst_291_, v_00_U0001d530_292_, v_T_293_);
lean_dec(v_T_293_);
lean_dec_ref(v_00_U0001d530_292_);
lean_dec(v_inst_291_);
lean_dec_ref(v_inst_290_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg___lam__0(lean_object* v_s_295_, lean_object* v_00_U0001d530_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_val_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_val_298_ = lean_ctor_get(v_s_295_, 0);
lean_inc(v_val_298_);
lean_dec_ref(v_s_295_);
lean_inc(v_a_297_);
v___x_299_ = lp_GRH_New_Shape_besselFrame(v_00_U0001d530_296_, v_a_297_);
v___x_300_ = l_Fin_succ___redArg(v_a_297_);
lean_dec(v_a_297_);
v___x_301_ = lp_GRH_New_Shape_besselFrame(v_00_U0001d530_296_, v___x_300_);
v___x_302_ = lean_apply_2(v_val_298_, v___x_299_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg___lam__0___boxed(lean_object* v_s_303_, lean_object* v_00_U0001d530_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = lp_GRH_New_simpleRootSum___redArg___lam__0(v_s_303_, v_00_U0001d530_304_, v_a_305_);
lean_dec_ref(v_00_U0001d530_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg(lean_object* v_inst_307_, lean_object* v_00_U0001d530_308_, lean_object* v_s_309_){
_start:
{
lean_object* v_toSemiring_310_; lean_object* v_toAddCommMonoid_311_; lean_object* v_00_u03f1_312_; lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_toSemiring_310_ = lean_ctor_get(v_inst_307_, 0);
v_toAddCommMonoid_311_ = lean_ctor_get(v_toSemiring_310_, 0);
v_00_u03f1_312_ = lean_ctor_get(v_00_U0001d530_308_, 0);
lean_inc(v_00_u03f1_312_);
v___f_313_ = lean_alloc_closure((void*)(lp_GRH_New_simpleRootSum___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_313_, 0, v_s_309_);
lean_closure_set(v___f_313_, 1, v_00_U0001d530_308_);
v___x_314_ = l_List_finRange(v_00_u03f1_312_);
v___x_315_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_311_, v___x_314_, v___f_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___redArg___boxed(lean_object* v_inst_316_, lean_object* v_00_U0001d530_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = lp_GRH_New_simpleRootSum___redArg(v_inst_316_, v_00_U0001d530_317_, v_s_318_);
lean_dec_ref(v_inst_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum(lean_object* v_R_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_00_U0001d530_323_, lean_object* v_T_324_, lean_object* v_s_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lp_GRH_New_simpleRootSum___redArg(v_inst_321_, v_00_U0001d530_323_, v_s_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_simpleRootSum___boxed(lean_object* v_R_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_00_U0001d530_330_, lean_object* v_T_331_, lean_object* v_s_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = lp_GRH_New_simpleRootSum(v_R_327_, v_inst_328_, v_inst_329_, v_00_U0001d530_330_, v_T_331_, v_s_332_);
lean_dec(v_T_331_);
lean_dec(v_inst_329_);
lean_dec_ref(v_inst_328_);
return v_res_333_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Witt_WittTheorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorGroups(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Adelic_Witt_WittTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
