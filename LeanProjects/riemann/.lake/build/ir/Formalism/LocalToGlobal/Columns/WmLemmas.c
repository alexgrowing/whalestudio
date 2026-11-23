// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.WmLemmas
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW public import Formalism.LocalToGlobal.Columns.HeckeSpCount public import Formalism.LocalToGlobal.Columns.HeckeSp public import Formalism.LocalToGlobal.Columns.MemWmPerp public import Formalism.LocalToGlobal.Columns.GSetLemmas
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__0(lean_object* v_toAddCommMonoid_1_, lean_object* v_x_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toZero_5_; 
v___x_4_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_1_);
v_toZero_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toZero_5_);
lean_dec_ref(v___x_4_);
return v_toZero_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_6_, lean_object* v_x_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__0(v_toAddCommMonoid_6_, v_x_7_, v___y_8_);
lean_dec(v___y_8_);
lean_dec(v_x_7_);
lean_dec_ref(v_toAddCommMonoid_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__1(lean_object* v___x_10_, lean_object* v___f_11_, lean_object* v_00_u03a6_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_14_; lean_object* v_toMul_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_14_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_10_);
v_toMul_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_toMul_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lean_apply_1(v_00_u03a6_12_, v___f_11_);
v___x_17_ = lean_apply_2(v_toMul_15_, v___x_16_, v___y_13_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg(lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_toCommRing_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toSemiring_25_; lean_object* v_toAddCommMonoid_26_; lean_object* v___f_27_; lean_object* v___f_28_; 
v_toCommRing_20_ = lean_ctor_get(v_inst_19_, 0);
v___x_21_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_20_);
v___x_22_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_21_);
v___x_23_ = lp_mathlib_Field_toSemifield___redArg(v_inst_18_);
v___x_24_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_23_);
v_toSemiring_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_toSemiring_25_);
lean_dec_ref(v___x_24_);
v_toAddCommMonoid_26_ = lean_ctor_get(v_toSemiring_25_, 0);
lean_inc_ref(v_toAddCommMonoid_26_);
lean_dec_ref(v_toSemiring_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_27_, 0, v_toAddCommMonoid_26_);
v___f_28_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_wmTh0___redArg___lam__1), 4, 2);
lean_closure_set(v___f_28_, 0, v___x_22_);
lean_closure_set(v___f_28_, 1, v___f_27_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___redArg___boxed(lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_Col_wmTh0___redArg(v_inst_29_, v_inst_30_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0(lean_object* v_E_32_, lean_object* v_K_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_a_37_, lean_object* v_b_38_, lean_object* v_SG_39_, lean_object* v_x_40_, lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_tree_Formalism_L2_Col_wmTh0___redArg(v_inst_34_, v_inst_36_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTh0___boxed(lean_object* v_E_44_, lean_object* v_K_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_a_49_, lean_object* v_b_50_, lean_object* v_SG_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_L2_Col_wmTh0(v_E_44_, v_K_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_a_49_, v_b_50_, v_SG_51_, v_x_52_, v_x_53_, v_x_54_);
lean_dec_ref(v_x_54_);
lean_dec_ref(v_x_53_);
lean_dec(v_x_52_);
lean_dec(v_SG_51_);
lean_dec(v_b_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_inst_48_);
lean_dec(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_UnipotentRightActionFunctionsW(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSpCount(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_MemWmPerp(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_WmLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_UnipotentRightActionFunctionsW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSpCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_MemWmPerp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
