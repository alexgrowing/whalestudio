// Lean compiler output
// Module: New.OneLift.FalseLifts.BottomOfTower
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.DescentVanishing public import New.UpperBound.Objects.AuxiliaryPair
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
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_GRH_New_inclMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_mulVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_vecMulVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_GRH_New_inclMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rowShear___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rowShear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__0(lean_object* v_00_u03b9_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_00_u03b9_1_, v___y_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__1(lean_object* v_toOne_4_, lean_object* v_x_5_){
_start:
{
lean_inc(v_toOne_4_);
return v_toOne_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__1___boxed(lean_object* v_toOne_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_completeColumns___redArg___lam__1(v_toOne_6_, v_x_7_);
lean_dec(v_x_7_);
lean_dec(v_toOne_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__2(lean_object* v_u_9_, lean_object* v_a_10_, lean_object* v_inst_11_, lean_object* v_toZero_12_, lean_object* v_toOne_13_, lean_object* v___f_14_, lean_object* v_toSub_15_, lean_object* v_j_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_inc(v_j_16_);
lean_inc(v_a_10_);
v___x_17_ = lean_apply_2(v_u_9_, v_a_10_, v_j_16_);
v___x_18_ = lp_GRH_New_inclMatrix___redArg(v_inst_11_, v_toZero_12_, v_toOne_13_, v___f_14_, v_a_10_, v_j_16_);
v___x_19_ = lean_apply_2(v_toSub_15_, v___x_17_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg___lam__3(lean_object* v___x_20_, lean_object* v_a_21_, lean_object* v_j_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_mathlib_Matrix_transpose___redArg(v___x_20_, v_j_22_, v_a_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns___redArg(lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_00_u03b9_27_, lean_object* v_u_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_toSemiring_31_; lean_object* v___x_32_; lean_object* v_toMul_33_; lean_object* v_toAdd_34_; lean_object* v___x_35_; lean_object* v_toZero_36_; lean_object* v___x_37_; lean_object* v_toAddMonoidWithOne_38_; lean_object* v_toOne_39_; lean_object* v_toAddCommMonoid_40_; lean_object* v___x_41_; lean_object* v_toSub_42_; lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_toSemiring_31_ = lean_ctor_get(v_inst_24_, 0);
lean_inc_ref_n(v_toSemiring_31_, 3);
v___x_32_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_31_);
v_toMul_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_toMul_33_);
v_toAdd_34_ = lean_ctor_get(v___x_32_, 1);
lean_inc(v_toAdd_34_);
lean_dec_ref(v___x_32_);
v___x_35_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_31_);
v_toZero_36_ = lean_ctor_get(v___x_35_, 1);
lean_inc_n(v_toZero_36_, 3);
lean_dec_ref(v___x_35_);
v___x_37_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_24_);
v_toAddMonoidWithOne_38_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_toAddMonoidWithOne_38_);
v_toOne_39_ = lean_ctor_get(v_toAddMonoidWithOne_38_, 2);
lean_inc_n(v_toOne_39_, 3);
lean_dec_ref(v_toAddMonoidWithOne_38_);
v_toAddCommMonoid_40_ = lean_ctor_get(v_toSemiring_31_, 0);
lean_inc_ref(v_toAddCommMonoid_40_);
lean_dec_ref(v_toSemiring_31_);
v___x_41_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_37_);
lean_dec_ref(v___x_37_);
v_toSub_42_ = lean_ctor_get(v___x_41_, 2);
lean_inc(v_toSub_42_);
lean_dec_ref(v___x_41_);
v___f_43_ = lean_alloc_closure((void*)(lp_GRH_New_completeColumns___redArg___lam__0), 2, 1);
lean_closure_set(v___f_43_, 0, v_00_u03b9_27_);
v___f_44_ = lean_alloc_closure((void*)(lp_GRH_New_completeColumns___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_44_, 0, v_toOne_39_);
lean_inc_ref(v___f_43_);
lean_inc_ref_n(v_inst_26_, 2);
lean_inc(v_a_29_);
v___f_45_ = lean_alloc_closure((void*)(lp_GRH_New_completeColumns___redArg___lam__2), 8, 7);
lean_closure_set(v___f_45_, 0, v_u_28_);
lean_closure_set(v___f_45_, 1, v_a_29_);
lean_closure_set(v___f_45_, 2, v_inst_26_);
lean_closure_set(v___f_45_, 3, v_toZero_36_);
lean_closure_set(v___f_45_, 4, v_toOne_39_);
lean_closure_set(v___f_45_, 5, v___f_43_);
lean_closure_set(v___f_45_, 6, v_toSub_42_);
v___x_46_ = lean_alloc_closure((void*)(lp_GRH_New_inclMatrix), 9, 7);
lean_closure_set(v___x_46_, 0, lean_box(0));
lean_closure_set(v___x_46_, 1, lean_box(0));
lean_closure_set(v___x_46_, 2, v_inst_26_);
lean_closure_set(v___x_46_, 3, lean_box(0));
lean_closure_set(v___x_46_, 4, v_toZero_36_);
lean_closure_set(v___x_46_, 5, v_toOne_39_);
lean_closure_set(v___x_46_, 6, v___f_43_);
lean_inc(v_a_30_);
v___f_47_ = lean_alloc_closure((void*)(lp_GRH_New_completeColumns___redArg___lam__3), 3, 2);
lean_closure_set(v___f_47_, 0, v___x_46_);
lean_closure_set(v___f_47_, 1, v_a_30_);
v___x_48_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_26_, v_toZero_36_, v___f_44_, v_a_29_, v_a_30_);
v___x_49_ = lp_mathlib_dotProduct___redArg(v_inst_25_, v_toMul_33_, v_toAddCommMonoid_40_, v___f_45_, v___f_47_);
lean_dec_ref(v_toAddCommMonoid_40_);
v___x_50_ = lean_apply_2(v_toAdd_34_, v___x_48_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_completeColumns(lean_object* v_R_51_, lean_object* v_r_52_, lean_object* v_n_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_00_u03b9_57_, lean_object* v_u_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_GRH_New_completeColumns___redArg(v_inst_54_, v_inst_55_, v_inst_56_, v_00_u03b9_57_, v_u_58_, v_a_59_, v_a_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rowShear___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_00_u03b9_65_, lean_object* v_v_66_, lean_object* v_l_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_toSemiring_70_; lean_object* v___x_71_; lean_object* v_toMul_72_; lean_object* v_toAdd_73_; lean_object* v___x_74_; lean_object* v_toZero_75_; lean_object* v___x_76_; lean_object* v_toAddMonoidWithOne_77_; lean_object* v_toOne_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_toSemiring_70_ = lean_ctor_get(v_inst_62_, 0);
lean_inc_ref_n(v_toSemiring_70_, 2);
v___x_71_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_70_);
v_toMul_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_toMul_72_);
v_toAdd_73_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_toAdd_73_);
lean_dec_ref(v___x_71_);
v___x_74_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_70_);
v_toZero_75_ = lean_ctor_get(v___x_74_, 1);
lean_inc_n(v_toZero_75_, 2);
lean_dec_ref(v___x_74_);
lean_inc_ref(v_inst_62_);
v___x_76_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_62_);
v_toAddMonoidWithOne_77_ = lean_ctor_get(v___x_76_, 1);
lean_inc_ref(v_toAddMonoidWithOne_77_);
lean_dec_ref(v___x_76_);
v_toOne_78_ = lean_ctor_get(v_toAddMonoidWithOne_77_, 2);
lean_inc_n(v_toOne_78_, 2);
lean_dec_ref(v_toAddMonoidWithOne_77_);
v___f_79_ = lean_alloc_closure((void*)(lp_GRH_New_completeColumns___redArg___lam__0), 2, 1);
lean_closure_set(v___f_79_, 0, v_00_u03b9_65_);
v___f_80_ = lean_alloc_closure((void*)(lp_GRH_New_completeColumns___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_80_, 0, v_toOne_78_);
v___x_81_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_62_);
lean_dec_ref(v_inst_62_);
v___x_82_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_81_);
lean_inc_ref(v_inst_64_);
v___x_83_ = lean_alloc_closure((void*)(lp_GRH_New_inclMatrix), 9, 7);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, lean_box(0));
lean_closure_set(v___x_83_, 2, v_inst_64_);
lean_closure_set(v___x_83_, 3, lean_box(0));
lean_closure_set(v___x_83_, 4, v_toZero_75_);
lean_closure_set(v___x_83_, 5, v_toOne_78_);
lean_closure_set(v___x_83_, 6, v___f_79_);
v___x_84_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_mulVec), 8, 7);
lean_closure_set(v___x_84_, 0, lean_box(0));
lean_closure_set(v___x_84_, 1, lean_box(0));
lean_closure_set(v___x_84_, 2, lean_box(0));
lean_closure_set(v___x_84_, 3, v___x_82_);
lean_closure_set(v___x_84_, 4, v_inst_63_);
lean_closure_set(v___x_84_, 5, v___x_83_);
lean_closure_set(v___x_84_, 6, v_v_66_);
lean_inc(v_a_69_);
lean_inc(v_a_68_);
v___x_85_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_64_, v_toZero_75_, v___f_80_, v_a_68_, v_a_69_);
v___x_86_ = lp_mathlib_Matrix_vecMulVec___redArg(v_toMul_72_, v___x_84_, v_l_67_, v_a_68_, v_a_69_);
v___x_87_ = lean_apply_2(v_toAdd_73_, v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rowShear(lean_object* v_R_88_, lean_object* v_r_89_, lean_object* v_n_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_00_u03b9_94_, lean_object* v_v_95_, lean_object* v_l_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_GRH_New_rowShear___redArg(v_inst_91_, v_inst_92_, v_inst_93_, v_00_u03b9_94_, v_v_95_, v_l_96_, v_a_97_, v_a_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup___redArg(){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(0);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup___redArg___boxed(lean_object* v___dummy_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_GRH_New_hyperplaneGroup___redArg();
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup(lean_object* v_k_104_, lean_object* v_r_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_l_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_hyperplaneGroup___boxed(lean_object* v_k_111_, lean_object* v_r_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_l_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_GRH_New_hyperplaneGroup(v_k_111_, v_r_112_, v_inst_113_, v_inst_114_, v_inst_115_, v_l_116_);
lean_dec(v_l_116_);
lean_dec_ref(v_inst_115_);
lean_dec(v_inst_114_);
lean_dec_ref(v_inst_113_);
return v_res_117_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_DescentVanishing(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_AuxiliaryPair(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_OneLift_FalseLifts_BottomOfTower(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_DescentVanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_AuxiliaryPair(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
