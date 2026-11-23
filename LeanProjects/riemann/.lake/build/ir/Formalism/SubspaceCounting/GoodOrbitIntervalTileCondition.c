// Lean compiler output
// Module: Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
// Imports: public import Init public meta import Init public import Formalism.SubspaceCounting.StatementC public import Formalism.SubspaceCounting.TopsChoiceSecondBound
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_cell(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_cell___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_markedBound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_markedBound___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_cell(lean_object* v_r_1_, lean_object* v_u_2_, lean_object* v_s_3_, lean_object* v_c_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_5_ = lean_unsigned_to_nat(6u);
v___x_6_ = lean_nat_mul(v___x_5_, v_r_1_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v___x_6_, v___x_7_);
lean_dec(v___x_6_);
v___x_9_ = lean_nat_mul(v___x_8_, v_u_2_);
lean_dec(v___x_8_);
v___x_10_ = lean_nat_mul(v_s_3_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = lean_nat_sub(v_c_4_, v___x_7_);
v___x_12_ = lean_nat_mul(v___x_11_, v_u_2_);
lean_dec(v___x_11_);
v___x_13_ = lean_nat_add(v___x_10_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_nat_mul(v_c_4_, v_u_2_);
v___x_15_ = lean_nat_add(v___x_10_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_10_);
v___x_16_ = lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(v___x_13_, v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_cell___boxed(lean_object* v_r_17_, lean_object* v_u_18_, lean_object* v_s_19_, lean_object* v_c_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_G0_cell(v_r_17_, v_u_18_, v_s_19_, v_c_20_);
lean_dec(v_c_20_);
lean_dec(v_s_19_);
lean_dec(v_u_18_);
lean_dec(v_r_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper___lam__0(lean_object* v_G_22_, lean_object* v_00_u03b4_23_, lean_object* v_j_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___f_30_; lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___f_34_; 
v___x_25_ = lp_mathlib_Nat_fast__choose(v_G_22_, v_j_24_);
v___x_26_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_25_);
lean_inc(v_00_u03b4_23_);
v___x_27_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v_j_24_, v_00_u03b4_23_);
v___f_28_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_28_, 0, v___x_26_);
lean_closure_set(v___f_28_, 1, v___x_27_);
v___x_29_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_30_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_30_, 0, v_00_u03b4_23_);
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_31_, 0, v___x_29_);
lean_closure_set(v___f_31_, 1, v___f_30_);
v___x_32_ = lean_nat_sub(v_G_22_, v_j_24_);
v___x_33_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_32_, v___f_31_);
lean_dec(v___x_32_);
v___f_34_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_34_, 0, v___f_28_);
lean_closure_set(v___f_34_, 1, v___x_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper___lam__0___boxed(lean_object* v_G_35_, lean_object* v_00_u03b4_36_, lean_object* v_j_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_G0_binUpper___lam__0(v_G_35_, v_00_u03b4_36_, v_j_37_);
lean_dec(v_j_37_);
lean_dec(v_G_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper(lean_object* v_G_39_, lean_object* v_00_u03b4_40_, lean_object* v_N_41_){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc(v_G_39_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_G0_binUpper___lam__0___boxed), 3, 2);
lean_closure_set(v___f_42_, 0, v_G_39_);
lean_closure_set(v___f_42_, 1, v_00_u03b4_40_);
v___x_43_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v_N_41_, v_G_39_);
lean_dec(v_G_39_);
v___x_44_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_43_, v___f_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binUpper___boxed(lean_object* v_G_45_, lean_object* v_00_u03b4_46_, lean_object* v_N_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree_Formalism_G0_binUpper(v_G_45_, v_00_u03b4_46_, v_N_47_);
lean_dec(v_N_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_markedBound(lean_object* v_00_u03b4_49_, lean_object* v_r_50_, lean_object* v_u_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___f_68_; 
v___x_52_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_inc(v_00_u03b4_49_);
v___f_53_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_53_, 0, v_00_u03b4_49_);
v___f_54_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_54_, 0, v___x_52_);
lean_closure_set(v___f_54_, 1, v___f_53_);
lean_inc_ref(v___f_54_);
v___x_55_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v_u_51_, v___f_54_);
v___x_56_ = lean_unsigned_to_nat(3u);
v___x_57_ = lean_nat_mul(v___x_56_, v_r_50_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v___x_57_, v___x_58_);
v___x_60_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_59_, v___x_55_);
lean_dec(v___x_59_);
v___x_61_ = lean_nat_shiftr(v_u_51_, v___x_58_);
v___x_62_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_61_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_63_, 0, v___x_62_);
lean_closure_set(v___f_63_, 1, v_00_u03b4_49_);
v___x_64_ = lean_nat_sub(v_u_51_, v___x_58_);
v___x_65_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_64_, v___f_54_);
lean_dec(v___x_64_);
v___f_66_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_66_, 0, v___f_63_);
lean_closure_set(v___f_66_, 1, v___x_65_);
v___x_67_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_57_, v___f_66_);
lean_dec(v___x_57_);
v___f_68_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_68_, 0, v___x_60_);
lean_closure_set(v___f_68_, 1, v___x_67_);
return v___f_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_markedBound___boxed(lean_object* v_00_u03b4_69_, lean_object* v_r_70_, lean_object* v_u_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_Formalism_G0_markedBound(v_00_u03b4_69_, v_r_70_, v_u_71_);
lean_dec(v_u_71_);
lean_dec(v_r_70_);
return v_res_72_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SubspaceCounting_StatementC(uint8_t builtin);
lean_object* initialize_tree_Formalism_SubspaceCounting_TopsChoiceSecondBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SubspaceCounting_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SubspaceCounting_TopsChoiceSecondBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
