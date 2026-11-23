// Lean compiler output
// Module: Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
// Imports: public import Init public meta import Init public import Mathlib public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.SpanNatCastLeComap
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
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0;
static lean_once_cell_t lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_truncLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_truncLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = l_Rat_instNatCast___lam__0(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0, &lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0_once, _init_lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0);
v___x_4_ = l_Rat_neg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0(lean_object* v_toNPow_5_, lean_object* v_x_6_, lean_object* v_toSMul_7_, lean_object* v_k_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_obj_once(&lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0, &lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0_once, _init_lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__0);
v___x_11_ = lean_obj_once(&lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__1, &lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__1_once, _init_lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0___closed__1);
v___x_12_ = l_Rat_pow(v___x_11_, v_k_8_);
lean_inc(v_k_8_);
v___x_13_ = l_Rat_instNatCast___lam__0(v_k_8_);
v___x_14_ = l_Rat_add(v___x_13_, v___x_10_);
v___x_15_ = l_Rat_div(v___x_12_, v___x_14_);
lean_dec_ref(v___x_12_);
v___x_16_ = lean_nat_add(v_k_8_, v___x_9_);
lean_dec(v_k_8_);
v___x_17_ = lean_apply_2(v_toNPow_5_, v___x_16_, v_x_6_);
v___x_18_ = lean_apply_2(v_toSMul_7_, v___x_15_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_truncLog___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_N_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_toSemiring_23_; lean_object* v_toMonoid_24_; lean_object* v_toAddCommMonoid_25_; lean_object* v_toSMul_26_; lean_object* v_toNPow_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
v_toSemiring_23_ = lean_ctor_get(v_inst_19_, 0);
lean_inc_ref(v_toSemiring_23_);
lean_dec_ref(v_inst_19_);
v_toMonoid_24_ = lean_ctor_get(v_toSemiring_23_, 1);
lean_inc_ref(v_toMonoid_24_);
v_toAddCommMonoid_25_ = lean_ctor_get(v_toSemiring_23_, 0);
lean_inc_ref(v_toAddCommMonoid_25_);
lean_dec_ref(v_toSemiring_23_);
v_toSMul_26_ = lean_ctor_get(v_inst_20_, 0);
lean_inc(v_toSMul_26_);
lean_dec_ref(v_inst_20_);
v_toNPow_27_ = lean_ctor_get(v_toMonoid_24_, 2);
lean_inc(v_toNPow_27_);
lean_dec_ref(v_toMonoid_24_);
v___x_28_ = l_List_range(v_N_21_);
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_truncLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_29_, 0, v_toNPow_27_);
lean_closure_set(v___f_29_, 1, v_x_22_);
lean_closure_set(v___f_29_, 2, v_toSMul_26_);
v___x_30_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_25_, v___x_28_, v___f_29_);
lean_dec_ref(v_toAddCommMonoid_25_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_truncLog(lean_object* v_B_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_N_34_, lean_object* v_x_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Reformulated_AutPerF_truncLog___redArg(v_inst_32_, v_inst_33_, v_N_34_, v_x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist___redArg___lam__0(lean_object* v_toSemiring_37_, lean_object* v_00_u03b7_38_, lean_object* v_00_u03d6_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_toMonoid_41_; lean_object* v_toSemigroup_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_toMonoid_41_ = lean_ctor_get(v_toSemiring_37_, 1);
lean_inc_ref(v_toMonoid_41_);
lean_dec_ref(v_toSemiring_37_);
v_toSemigroup_42_ = lean_ctor_get(v_toMonoid_41_, 0);
lean_inc(v_toSemigroup_42_);
lean_dec_ref(v_toMonoid_41_);
lean_inc(v___y_40_);
v___x_43_ = lean_apply_1(v_00_u03b7_38_, v___y_40_);
v___x_44_ = lean_apply_1(v_00_u03d6_39_, v___y_40_);
v___x_45_ = lean_apply_2(v_toSemigroup_42_, v___x_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist___redArg(lean_object* v_inst_46_, lean_object* v_00_u03b7_47_, lean_object* v_00_u03d6_48_){
_start:
{
lean_object* v_toSemiring_49_; lean_object* v___f_50_; 
v_toSemiring_49_ = lean_ctor_get(v_inst_46_, 0);
lean_inc_ref(v_toSemiring_49_);
lean_dec_ref(v_inst_46_);
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_PFlat_twist___redArg___lam__0), 4, 3);
lean_closure_set(v___f_50_, 0, v_toSemiring_49_);
lean_closure_set(v___f_50_, 1, v_00_u03b7_47_);
lean_closure_set(v___f_50_, 2, v_00_u03d6_48_);
return v___f_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist(lean_object* v_p_51_, lean_object* v_inst_52_, lean_object* v_R_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_00_u03b7_57_, lean_object* v_00_u03d6_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Reformulated_AutPerF_PFlat_twist___redArg(v_inst_54_, v_00_u03b7_57_, v_00_u03d6_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_twist___boxed(lean_object* v_p_60_, lean_object* v_inst_61_, lean_object* v_R_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_00_u03b7_66_, lean_object* v_00_u03d6_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Reformulated_AutPerF_PFlat_twist(v_p_60_, v_inst_61_, v_R_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_00_u03b7_66_, v_00_u03d6_67_);
lean_dec(v_p_60_);
return v_res_68_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero(uint8_t builtin) {
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
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
