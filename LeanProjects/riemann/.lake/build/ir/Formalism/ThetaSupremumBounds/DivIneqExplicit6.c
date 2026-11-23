// Lean compiler output
// Module: Formalism.ThetaSupremumBounds.DivIneqExplicit6
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.StatementK public import Formalism.ThetaSupremumBounds.StatementC public import Formalism.ThetaSupremumBounds.StatementE
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordA___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordX___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_DimensionVariation_recordX___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DimensionVariation_recordX___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_DimensionVariation_recordX___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordX___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordA___redArg___lam__0(lean_object* v_aT_1_, lean_object* v_logT_2_, lean_object* v_t_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___f_5_; 
v___x_4_ = lean_apply_1(v_aT_1_, v_t_3_);
v___f_5_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_5_, 0, v___x_4_);
lean_closure_set(v___f_5_, 1, v_logT_2_);
return v___f_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordA___redArg(lean_object* v_TT_6_, lean_object* v_aT_7_, lean_object* v_logT_8_, lean_object* v_f_9_, lean_object* v_m_10_, lean_object* v_N_11_, lean_object* v_S_12_, lean_object* v_00_u03b7_13_, lean_object* v_b_x27_14_, lean_object* v_La_15_, lean_object* v_C_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___f_35_; 
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_DimensionVariation_recordA___redArg___lam__0), 3, 2);
lean_closure_set(v___f_17_, 0, v_aT_7_);
lean_closure_set(v___f_17_, 1, v_logT_8_);
lean_inc(v_TT_6_);
v___x_18_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v_TT_6_, v___f_17_);
v___f_19_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_19_, 0, v___x_18_);
v___x_20_ = l_List_lengthTR___redArg(v_TT_6_);
lean_dec(v_TT_6_);
v___x_21_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_22_, 0, v___x_21_);
lean_closure_set(v___f_22_, 1, v_b_x27_14_);
lean_inc_n(v_N_11_, 2);
v___f_23_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_23_, 0, v___f_22_);
lean_closure_set(v___f_23_, 1, v_N_11_);
v___f_24_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_24_, 0, v_m_10_);
lean_closure_set(v___f_24_, 1, v_00_u03b7_13_);
v___f_25_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_25_, 0, v___f_24_);
lean_closure_set(v___f_25_, 1, v_S_12_);
lean_inc(v_f_9_);
v___f_26_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_26_, 0, v_f_9_);
lean_closure_set(v___f_26_, 1, v___f_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_27_, 0, v___f_26_);
lean_closure_set(v___f_27_, 1, v_N_11_);
v___f_28_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_28_, 0, v___f_23_);
lean_closure_set(v___f_28_, 1, v___f_27_);
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_29_, v_N_11_);
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_31_, 0, v_f_9_);
lean_closure_set(v___f_31_, 1, v___x_30_);
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_32_, 0, v___f_28_);
lean_closure_set(v___f_32_, 1, v___f_31_);
v___f_33_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_33_, 0, v_C_16_);
lean_closure_set(v___f_33_, 1, v___f_32_);
v___f_34_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_34_, 0, v___f_33_);
lean_closure_set(v___f_34_, 1, v_La_15_);
v___f_35_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_35_, 0, v___f_19_);
lean_closure_set(v___f_35_, 1, v___f_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordA(lean_object* v_Pl_36_, lean_object* v_TT_37_, lean_object* v_aT_38_, lean_object* v_logT_39_, lean_object* v_f_40_, lean_object* v_m_41_, lean_object* v_N_42_, lean_object* v_S_43_, lean_object* v_00_u03b7_44_, lean_object* v_b_x27_45_, lean_object* v_La_46_, lean_object* v_C_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_DimensionVariation_recordA___redArg(v_TT_37_, v_aT_38_, v_logT_39_, v_f_40_, v_m_41_, v_N_42_, v_S_43_, v_00_u03b7_44_, v_b_x27_45_, v_La_46_, v_C_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordX___redArg___lam__0(lean_object* v_logH_49_, lean_object* v_j_50_, lean_object* v_00_u03c1_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_apply_2(v_logH_49_, v_j_50_, v_00_u03c1_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordX___redArg(lean_object* v_inst_54_, lean_object* v_logH_55_, lean_object* v_f_56_, lean_object* v_nV_57_, lean_object* v_L_x27_58_, lean_object* v_C_59_, lean_object* v_j_60_){
_start:
{
lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___f_72_; 
v___f_61_ = lean_alloc_closure((void*)(lp_tree_Formalism_DimensionVariation_recordX___redArg___lam__0), 3, 2);
lean_closure_set(v___f_61_, 0, v_logH_55_);
lean_closure_set(v___f_61_, 1, v_j_60_);
v___f_62_ = ((lean_object*)(lp_tree_Formalism_DimensionVariation_recordX___redArg___closed__0));
v___x_63_ = lp_mathlib_Real_instAddCommMonoid;
v___x_64_ = lp_mathlib_Finset_sum___redArg(v___x_63_, v_inst_54_, v___f_61_);
v___f_65_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_65_, 0, v_C_59_);
lean_closure_set(v___f_65_, 1, v_f_56_);
v___x_66_ = lean_unsigned_to_nat(2u);
v___x_67_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_68_ = l_npowRec___redArg(v___x_67_, v___f_62_, v___x_66_, v_nV_57_);
v___f_69_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_69_, 0, v___f_65_);
lean_closure_set(v___f_69_, 1, v___x_68_);
v___f_70_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_70_, 0, v___f_69_);
lean_closure_set(v___f_70_, 1, v_L_x27_58_);
v___f_71_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_71_, 0, v___f_70_);
v___f_72_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_72_, 0, v___x_64_);
lean_closure_set(v___f_72_, 1, v___f_71_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_recordX(lean_object* v_J_73_, lean_object* v_Pl_74_, lean_object* v_inst_75_, lean_object* v_logH_76_, lean_object* v_f_77_, lean_object* v_nV_78_, lean_object* v_L_x27_79_, lean_object* v_C_80_, lean_object* v_j_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lp_tree_Formalism_DimensionVariation_recordX___redArg(v_inst_75_, v_logH_76_, v_f_77_, v_nV_78_, v_L_x27_79_, v_C_80_, v_j_81_);
return v___x_82_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_StatementK(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_StatementC(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_StatementE(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaSupremumBounds_DivIneqExplicit6(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_StatementK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
