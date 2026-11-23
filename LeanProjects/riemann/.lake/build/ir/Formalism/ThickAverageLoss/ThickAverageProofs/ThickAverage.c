// Lean compiler output
// Module: Formalism.ThickAverageLoss.ThickAverageProofs.ThickAverage
// Imports: public import Init public meta import Init public import Formalism.ThickAverageLoss.ParametersAveragedDifferenceBound public import Formalism.ThickAverageLoss.PartnersToFactorsAt
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
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_D5_e10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_e10___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_D5_e10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_e10___redArg___closed__1;
static lean_once_cell_t lp_tree_Formalism_D5_e10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_e10___redArg___closed__2;
static lean_once_cell_t lp_tree_Formalism_D5_e10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_e10___redArg___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_D5_e10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_ZMod_instField___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_e10___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__0, &lp_tree_Formalism_D5_e10___redArg___closed__0_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__0);
v___x_4_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_e10___redArg___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__0, &lp_tree_Formalism_D5_e10___redArg___closed__0_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__0);
v___x_6_ = lp_mathlib_Field_toSemifield___redArg(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_e10___redArg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__2, &lp_tree_Formalism_D5_e10___redArg___closed__2_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__2);
v___x_8_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10___redArg(lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; lean_object* v_toRing_11_; lean_object* v___x_12_; lean_object* v_toAddMonoidWithOne_13_; lean_object* v_toOne_14_; lean_object* v___x_15_; lean_object* v_toSemiring_16_; lean_object* v___x_17_; lean_object* v_toZero_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_35_; 
v___x_10_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__1, &lp_tree_Formalism_D5_e10___redArg___closed__1_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__1);
v_toRing_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_ref(v_toRing_11_);
v___x_12_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_11_);
v_toAddMonoidWithOne_13_ = lean_ctor_get(v___x_12_, 1);
lean_inc_ref(v_toAddMonoidWithOne_13_);
lean_dec_ref(v___x_12_);
v_toOne_14_ = lean_ctor_get(v_toAddMonoidWithOne_13_, 2);
lean_inc(v_toOne_14_);
lean_dec_ref(v_toAddMonoidWithOne_13_);
v___x_15_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__3, &lp_tree_Formalism_D5_e10___redArg___closed__3_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__3);
v_toSemiring_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_toSemiring_16_);
v___x_17_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_16_);
v_toZero_18_ = lean_ctor_get(v___x_17_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_35_ == 0)
{
lean_object* v_unused_36_; 
v_unused_36_ = lean_ctor_get(v___x_17_, 0);
lean_dec(v_unused_36_);
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_35_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_toZero_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_35_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v_toZero_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_33_; 
v___x_22_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_inst_9_);
v_toZero_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_33_ == 0)
{
lean_object* v_unused_34_; 
v_unused_34_ = lean_ctor_get(v___x_22_, 1);
lean_dec(v_unused_34_);
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_33_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_toZero_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_33_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_toZero_18_);
lean_ctor_set(v___x_25_, 0, v_toOne_14_);
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_toOne_14_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_toZero_18_);
v___x_28_ = v_reuseFailAlloc_32_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_30_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v_toZero_23_);
lean_ctor_set(v___x_20_, 0, v___x_28_);
v___x_30_ = v___x_20_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_toZero_23_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10___redArg___boxed(lean_object* v_inst_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_D5_e10___redArg(v_inst_37_);
lean_dec_ref(v_inst_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10(lean_object* v_H_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Formalism_D5_e10___redArg(v_inst_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e10___boxed(lean_object* v_H_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_D5_e10(v_H_42_, v_inst_43_);
lean_dec_ref(v_inst_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01___redArg(lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; lean_object* v_toSemiring_47_; lean_object* v___x_48_; lean_object* v_toZero_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_71_; 
v___x_46_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__3, &lp_tree_Formalism_D5_e10___redArg___closed__3_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__3);
v_toSemiring_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_toSemiring_47_);
v___x_48_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_47_);
v_toZero_49_ = lean_ctor_get(v___x_48_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v___x_48_, 0);
lean_dec(v_unused_72_);
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_71_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_toZero_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_71_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v_toRing_54_; lean_object* v___x_55_; lean_object* v_toAddMonoidWithOne_56_; lean_object* v_toOne_57_; lean_object* v___x_58_; lean_object* v_toZero_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_69_; 
v___x_53_ = lean_obj_once(&lp_tree_Formalism_D5_e10___redArg___closed__1, &lp_tree_Formalism_D5_e10___redArg___closed__1_once, _init_lp_tree_Formalism_D5_e10___redArg___closed__1);
v_toRing_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref(v_toRing_54_);
v___x_55_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_54_);
v_toAddMonoidWithOne_56_ = lean_ctor_get(v___x_55_, 1);
lean_inc_ref(v_toAddMonoidWithOne_56_);
lean_dec_ref(v___x_55_);
v_toOne_57_ = lean_ctor_get(v_toAddMonoidWithOne_56_, 2);
lean_inc(v_toOne_57_);
lean_dec_ref(v_toAddMonoidWithOne_56_);
v___x_58_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_inst_45_);
v_toZero_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; 
v_unused_70_ = lean_ctor_get(v___x_58_, 1);
lean_dec(v_unused_70_);
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_69_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_toZero_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_69_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_toOne_57_);
lean_ctor_set(v___x_61_, 0, v_toZero_49_);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_toZero_49_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_toOne_57_);
v___x_64_ = v_reuseFailAlloc_68_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v_toZero_59_);
lean_ctor_set(v___x_51_, 0, v___x_64_);
v___x_66_ = v___x_51_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_toZero_59_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01___redArg___boxed(lean_object* v_inst_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_D5_e01___redArg(v_inst_73_);
lean_dec_ref(v_inst_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01(lean_object* v_H_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_tree_Formalism_D5_e01___redArg(v_inst_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_e01___boxed(lean_object* v_H_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_tree_Formalism_D5_e01(v_H_78_, v_inst_79_);
lean_dec_ref(v_inst_79_);
return v_res_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThickAverageLoss_PartnersToFactorsAt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThickAverageLoss_PartnersToFactorsAt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
