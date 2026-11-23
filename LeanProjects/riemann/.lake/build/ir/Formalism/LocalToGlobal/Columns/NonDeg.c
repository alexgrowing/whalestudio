// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.NonDeg
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.AtTRank public import Formalism.LocalToGlobal.Columns.ToHLatLemmas public import Formalism.LocalToGlobal.Columns.CoefficientsModP public import Formalism.LocalToGlobal.Columns.ColFormsInst public import Formalism.LocalToGlobal.Columns.AtTOwedS public import Formalism.LocalToGlobal.Columns.RamifiedOperatorsNonvacuous
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ndPowMod(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ndPowMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_ndN___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_ndN___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ndN;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ndPowMod(lean_object* v_m_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_zero_5_; uint8_t v_isZero_6_; 
v_zero_5_ = lean_unsigned_to_nat(0u);
v_isZero_6_ = lean_nat_dec_eq(v_x_2_, v_zero_5_);
if (v_isZero_6_ == 1)
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(1u);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___y_11_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_x_2_, v_one_8_);
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_nat_mod(v_x_4_, v___x_18_);
v___x_20_ = lean_nat_dec_eq(v___x_19_, v_one_8_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
v___y_11_ = v_one_8_;
goto v___jp_10_;
}
else
{
v___y_11_ = v_x_3_;
goto v___jp_10_;
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_12_ = lean_nat_mul(v_x_3_, v_x_3_);
v___x_13_ = lean_nat_mod(v___x_12_, v_m_1_);
lean_dec(v___x_12_);
v___x_14_ = lean_nat_shiftr(v_x_4_, v_one_8_);
v___x_15_ = lp_tree_Formalism_L2_Col_ndPowMod(v_m_1_, v_n_9_, v___x_13_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_13_);
lean_dec(v_n_9_);
v___x_16_ = lean_nat_mul(v___y_11_, v___x_15_);
lean_dec(v___x_15_);
v___x_17_ = lean_nat_mod(v___x_16_, v_m_1_);
lean_dec(v___x_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ndPowMod___boxed(lean_object* v_m_21_, lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_L2_Col_ndPowMod(v_m_21_, v_x_22_, v_x_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_x_23_);
lean_dec(v_x_22_);
lean_dec(v_m_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___redArg(lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
lean_object* v_zero_31_; uint8_t v_isZero_32_; 
v_zero_31_ = lean_unsigned_to_nat(0u);
v_isZero_32_ = lean_nat_dec_eq(v_x_26_, v_zero_31_);
if (v_isZero_32_ == 1)
{
lean_object* v___x_33_; 
lean_dec(v_h__2_30_);
v___x_33_ = lean_apply_2(v_h__1_29_, v_x_27_, v_x_28_);
return v___x_33_;
}
else
{
lean_object* v_one_34_; lean_object* v_n_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_29_);
v_one_34_ = lean_unsigned_to_nat(1u);
v_n_35_ = lean_nat_sub(v_x_26_, v_one_34_);
v___x_36_ = lean_apply_3(v_h__2_30_, v_n_35_, v_x_27_, v_x_28_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___redArg___boxed(lean_object* v_x_37_, lean_object* v_x_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___redArg(v_x_37_, v_x_38_, v_x_39_, v_h__1_40_, v_h__2_41_);
lean_dec(v_x_37_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter(lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v_zero_49_; uint8_t v_isZero_50_; 
v_zero_49_ = lean_unsigned_to_nat(0u);
v_isZero_50_ = lean_nat_dec_eq(v_x_44_, v_zero_49_);
if (v_isZero_50_ == 1)
{
lean_object* v___x_51_; 
lean_dec(v_h__2_48_);
v___x_51_ = lean_apply_2(v_h__1_47_, v_x_45_, v_x_46_);
return v___x_51_;
}
else
{
lean_object* v_one_52_; lean_object* v_n_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_47_);
v_one_52_ = lean_unsigned_to_nat(1u);
v_n_53_ = lean_nat_sub(v_x_44_, v_one_52_);
v___x_54_ = lean_apply_3(v_h__2_48_, v_n_53_, v_x_45_, v_x_46_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter___boxed(lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree___private_Formalism_LocalToGlobal_Columns_NonDeg_0__Formalism_L2_Col_ndPowMod_match__1_splitter(v_motive_55_, v_x_56_, v_x_57_, v_x_58_, v_h__1_59_, v_h__2_60_);
lean_dec(v_x_56_);
return v_res_61_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_ndN___closed__0(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_cstr_to_nat("206453207253716297532");
return v___x_62_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_ndN(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&lp_tree_Formalism_L2_Col_ndN___closed__0, &lp_tree_Formalism_L2_Col_ndN___closed__0_once, _init_lp_tree_Formalism_L2_Col_ndN___closed__0);
return v___x_63_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AtTRank(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ToHLatLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsInst(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AtTOwedS(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RamifiedOperatorsNonvacuous(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_NonDeg(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_AtTRank(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ToHLatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsInst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AtTOwedS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RamifiedOperatorsNonvacuous(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Formalism_L2_Col_ndN = _init_lp_tree_Formalism_L2_Col_ndN();
lean_mark_persistent(lp_tree_Formalism_L2_Col_ndN);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
