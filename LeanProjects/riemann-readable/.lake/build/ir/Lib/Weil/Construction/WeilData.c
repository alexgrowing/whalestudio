// Lean compiler output
// Module: Lib.Weil.Construction.WeilData
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.GramMatrix public import Lib.ClassField.HeckeCharacter.Basic public import Lib.Weil.Construction.HeisenbergModel
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
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_WeilData_traceOne___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_WeilData_traceOne(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_WeilData_traceOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_WeilData_traceOne___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v_toDiv_5_; lean_object* v_toRing_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toAddMonoidWithOne_9_; lean_object* v_toSub_10_; lean_object* v_toNatCast_11_; lean_object* v_toOne_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toInv_17_; lean_object* v_j_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
lean_inc_ref(v_inst_1_);
v___x_3_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v___x_4_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_3_);
v_toDiv_5_ = lean_ctor_get(v___x_4_, 2);
lean_inc(v_toDiv_5_);
lean_dec_ref(v___x_4_);
v_toRing_6_ = lean_ctor_get(v___x_3_, 0);
lean_inc_ref(v_toRing_6_);
lean_dec_ref(v___x_3_);
v___x_7_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_6_);
v___x_8_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_7_);
v_toAddMonoidWithOne_9_ = lean_ctor_get(v___x_7_, 1);
lean_inc_ref(v_toAddMonoidWithOne_9_);
lean_dec_ref(v___x_7_);
v_toSub_10_ = lean_ctor_get(v___x_8_, 2);
lean_inc(v_toSub_10_);
lean_dec_ref(v___x_8_);
v_toNatCast_11_ = lean_ctor_get(v_toAddMonoidWithOne_9_, 0);
lean_inc(v_toNatCast_11_);
v_toOne_12_ = lean_ctor_get(v_toAddMonoidWithOne_9_, 2);
lean_inc(v_toOne_12_);
lean_dec_ref(v_toAddMonoidWithOne_9_);
v___x_13_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
lean_dec_ref(v_inst_1_);
v___x_14_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_13_);
lean_dec_ref(v___x_13_);
v___x_15_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_14_);
v___x_16_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_15_);
lean_dec_ref(v___x_15_);
v_toInv_17_ = lean_ctor_get(v___x_16_, 1);
lean_inc(v_toInv_17_);
lean_dec_ref(v___x_16_);
v_j_18_ = lean_ctor_get(v_inst_2_, 1);
lean_inc(v_j_18_);
lean_dec_ref(v_inst_2_);
v___x_19_ = lean_apply_1(v_toInv_17_, v_j_18_);
v___x_20_ = lean_apply_2(v_toSub_10_, v_toOne_12_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_apply_1(v_toNatCast_11_, v___x_21_);
v___x_23_ = lean_apply_2(v_toDiv_5_, v___x_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_WeilData_traceOne(lean_object* v_E_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GRH_New_WeilData_traceOne___redArg(v_inst_25_, v_inst_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_WeilData_traceOne___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_WeilData_traceOne(v_E_29_, v_inst_30_, v_inst_31_, v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_GramMatrix(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_HeisenbergModel(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Construction_WeilData(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_GramMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_HeckeCharacter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Construction_HeisenbergModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
