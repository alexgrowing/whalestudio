// Lean compiler output
// Module: New.Spanning.Frames.FiberMeasures
// Imports: public import Init public meta import Init public import New.Spanning.Frames.StandardLevel
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_GRH_New_Floors_Place_skewUnitMul___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_GRH_New_middleInclusionMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_scalar___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromRows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromCols___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_lastEntrySphereIndex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_lastEntrySphereIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_lastEntrySphereIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_middleBasisMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_middleBasisMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_middleBasisMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_lastEntrySphereIndex___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_P_3_, lean_object* v_00_u03c0_4_, lean_object* v_t_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toSub_8_; lean_object* v_toSemiring_9_; lean_object* v___x_10_; lean_object* v_toMul_11_; lean_object* v_toMonoid_12_; lean_object* v_val_13_; lean_object* v_inv_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toMul_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_inc_ref(v_inst_1_);
v___x_6_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v___x_7_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_6_);
lean_dec_ref(v___x_6_);
v_toSub_8_ = lean_ctor_get(v___x_7_, 2);
lean_inc(v_toSub_8_);
lean_dec_ref(v___x_7_);
v_toSemiring_9_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_9_);
v___x_10_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_9_);
v_toMul_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_n(v_toMul_11_, 3);
lean_dec_ref(v___x_10_);
v_toMonoid_12_ = lean_ctor_get(v_toSemiring_9_, 1);
v_val_13_ = lean_ctor_get(v_00_u03c0_4_, 0);
lean_inc_n(v_val_13_, 2);
v_inv_14_ = lean_ctor_get(v_00_u03c0_4_, 1);
lean_inc_n(v_inv_14_, 2);
lean_dec_ref(v_00_u03c0_4_);
v___x_15_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_12_);
v___x_16_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_15_);
v_toMul_17_ = lean_ctor_get(v___x_16_, 1);
lean_inc(v_toMul_17_);
lean_dec_ref(v___x_16_);
lean_inc_n(v_inst_2_, 2);
v___x_18_ = lean_apply_1(v_inst_2_, v_inv_14_);
v___x_19_ = lean_apply_2(v_toMul_17_, v___x_18_, v_inv_14_);
lean_inc(v_t_5_);
v___x_20_ = lean_apply_2(v_toMul_11_, v___x_19_, v_t_5_);
v___x_21_ = lean_apply_1(v_inst_2_, v_t_5_);
v___x_22_ = lean_apply_2(v_toMul_11_, v___x_20_, v___x_21_);
v___x_23_ = lean_apply_1(v_inst_2_, v_val_13_);
v___x_24_ = lean_apply_2(v_toMul_11_, v_val_13_, v___x_23_);
v___x_25_ = lean_apply_2(v_toSub_8_, v___x_22_, v___x_24_);
v___x_26_ = lp_GRH_New_Floors_Place_skewUnitMul___redArg(v_inst_1_, v_P_3_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_lastEntrySphereIndex(lean_object* v_A_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_P_32_, lean_object* v_00_u03c0_33_, lean_object* v_t_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_GRH_New_Floors_lastEntrySphereIndex___redArg(v_inst_28_, v_inst_29_, v_P_32_, v_00_u03c0_33_, v_t_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_lastEntrySphereIndex___boxed(lean_object* v_A_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_P_41_, lean_object* v_00_u03c0_42_, lean_object* v_t_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_Floors_lastEntrySphereIndex(v_A_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_P_41_, v_00_u03c0_42_, v_t_43_);
lean_dec_ref(v_inst_40_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_middleBasisMatrix___redArg___lam__0(lean_object* v_toSemiring_45_, lean_object* v___x_46_, lean_object* v_inv_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_72__overap_50_; lean_object* v___x_51_; 
v___x_72__overap_50_ = lp_mathlib_Matrix_scalar___redArg(v_toSemiring_45_, v___x_46_);
v___x_51_ = lean_apply_3(v___x_72__overap_50_, v_inv_47_, v___y_48_, v___y_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_middleBasisMatrix___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_00_U0001d530_54_, lean_object* v_00_u03c0_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_toSemiring_58_; lean_object* v___x_59_; lean_object* v_toZero_60_; lean_object* v_inv_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_toSemiring_58_ = lean_ctor_get(v_inst_52_, 0);
lean_inc_ref_n(v_toSemiring_58_, 2);
v___x_59_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_58_);
v_toZero_60_ = lean_ctor_get(v___x_59_, 1);
lean_inc(v_toZero_60_);
lean_dec_ref(v___x_59_);
v_inv_61_ = lean_ctor_get(v_00_u03c0_55_, 1);
lean_inc(v_inv_61_);
v___x_62_ = lean_alloc_closure((void*)(lp_GRH_New_middleInclusionMatrix), 7, 5);
lean_closure_set(v___x_62_, 0, lean_box(0));
lean_closure_set(v___x_62_, 1, v_inst_52_);
lean_closure_set(v___x_62_, 2, v_00_U0001d530_54_);
lean_closure_set(v___x_62_, 3, v_inst_53_);
lean_closure_set(v___x_62_, 4, v_00_u03c0_55_);
v___x_63_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_63_, 0, lean_box(0));
lean_closure_set(v___x_63_, 1, lean_box(0));
lean_closure_set(v___x_63_, 2, lean_box(0));
lean_closure_set(v___x_63_, 3, v_toZero_60_);
v___x_64_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_65_ = lean_alloc_closure((void*)(lp_GRH_New_Floors_middleBasisMatrix___redArg___lam__0), 5, 3);
lean_closure_set(v___f_65_, 0, v_toSemiring_58_);
lean_closure_set(v___f_65_, 1, v___x_64_);
lean_closure_set(v___f_65_, 2, v_inv_61_);
v___x_66_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromRows), 8, 6);
lean_closure_set(v___x_66_, 0, lean_box(0));
lean_closure_set(v___x_66_, 1, lean_box(0));
lean_closure_set(v___x_66_, 2, lean_box(0));
lean_closure_set(v___x_66_, 3, lean_box(0));
lean_closure_set(v___x_66_, 4, v___x_63_);
lean_closure_set(v___x_66_, 5, v___f_65_);
v___x_67_ = lp_mathlib_Matrix_fromCols___redArg(v___x_62_, v___x_66_, v_a_56_, v_a_57_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_middleBasisMatrix(lean_object* v_A_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_00_U0001d530_71_, lean_object* v_00_u03c0_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_GRH_New_Floors_middleBasisMatrix___redArg(v_inst_69_, v_inst_70_, v_00_U0001d530_71_, v_00_u03c0_72_, v_a_73_, v_a_74_);
return v___x_75_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Frames_StandardLevel(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Frames_FiberMeasures(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_Frames_StandardLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
