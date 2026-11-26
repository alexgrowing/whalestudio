// Lean compiler output
// Module: New.UpperBound.Divisibility.HeckeEdges
// Imports: public import Init public meta import Init public import New.UpperBound.Divisibility.MarkedPrimes public import New.UpperBound.ElementaryDivisors.ElementaryDivisorTheorem
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_DivisionSemiring_toGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_mathlib_Units_mk0___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_diagGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___redArg___lam__0(lean_object* v_q_1_, lean_object* v_r_2_, lean_object* v_toMonoid_3_, lean_object* v_toNatCast_4_, lean_object* v_p_5_, lean_object* v___x_6_, lean_object* v_i_7_){
_start:
{
lean_object* v_toFun_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_toFun_8_ = lean_ctor_get(v_q_1_, 0);
lean_inc(v_toFun_8_);
lean_dec_ref(v_q_1_);
v___x_9_ = lean_apply_1(v_toFun_8_, v_i_7_);
v___x_10_ = lean_nat_dec_lt(v___x_9_, v_r_2_);
lean_dec(v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toOne_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_20_; 
lean_dec_ref(v___x_6_);
lean_dec(v_p_5_);
lean_dec(v_toNatCast_4_);
v___x_11_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_3_);
v___x_12_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_11_);
v_toOne_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_20_ == 0)
{
lean_object* v_unused_21_; 
v_unused_21_ = lean_ctor_get(v___x_12_, 1);
lean_dec(v_unused_21_);
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_toOne_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
lean_inc(v_toOne_13_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v_toOne_13_);
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_toOne_13_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_toOne_13_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_apply_1(v_toNatCast_4_, v_p_5_);
v___x_23_ = lp_mathlib_Units_mk0___redArg(v___x_6_, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___redArg___lam__0___boxed(lean_object* v_q_24_, lean_object* v_r_25_, lean_object* v_toMonoid_26_, lean_object* v_toNatCast_27_, lean_object* v_p_28_, lean_object* v___x_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_GRH_New_Columns_blockScaling___redArg___lam__0(v_q_24_, v_r_25_, v_toMonoid_26_, v_toNatCast_27_, v_p_28_, v___x_29_, v_i_30_);
lean_dec_ref(v_toMonoid_26_);
lean_dec(v_r_25_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___redArg(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_q_34_, lean_object* v_p_35_, lean_object* v_r_36_){
_start:
{
lean_object* v_toCommRing_37_; lean_object* v_toSemiring_38_; lean_object* v_toMonoid_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_toRing_44_; lean_object* v___x_45_; lean_object* v_toAddMonoidWithOne_46_; lean_object* v_toNatCast_47_; lean_object* v___f_48_; lean_object* v___x_64__overap_49_; lean_object* v___x_50_; 
v_toCommRing_37_ = lean_ctor_get(v_inst_32_, 0);
lean_inc_ref(v_toCommRing_37_);
v_toSemiring_38_ = lean_ctor_get(v_toCommRing_37_, 0);
v_toMonoid_39_ = lean_ctor_get(v_toSemiring_38_, 1);
v___x_40_ = lp_mathlib_Field_toSemifield___redArg(v_inst_32_);
v___x_41_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_40_);
v___x_42_ = lp_mathlib_DivisionSemiring_toGroupWithZero___redArg(v___x_41_);
lean_dec_ref(v___x_41_);
v___x_43_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_32_);
v_toRing_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_toRing_44_);
lean_dec_ref(v___x_43_);
v___x_45_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_44_);
v_toAddMonoidWithOne_46_ = lean_ctor_get(v___x_45_, 1);
lean_inc_ref(v_toAddMonoidWithOne_46_);
lean_dec_ref(v___x_45_);
v_toNatCast_47_ = lean_ctor_get(v_toAddMonoidWithOne_46_, 0);
lean_inc(v_toNatCast_47_);
lean_dec_ref(v_toAddMonoidWithOne_46_);
lean_inc_ref(v_toMonoid_39_);
v___f_48_ = lean_alloc_closure((void*)(lp_GRH_New_Columns_blockScaling___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_48_, 0, v_q_34_);
lean_closure_set(v___f_48_, 1, v_r_36_);
lean_closure_set(v___f_48_, 2, v_toMonoid_39_);
lean_closure_set(v___f_48_, 3, v_toNatCast_47_);
lean_closure_set(v___f_48_, 4, v_p_35_);
lean_closure_set(v___f_48_, 5, v___x_42_);
v___x_64__overap_49_ = lp_GRH_New_diagGL___redArg(v_inst_33_, v_toCommRing_37_);
v___x_50_ = lean_apply_1(v___x_64__overap_49_, v___f_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling(lean_object* v_E_51_, lean_object* v_n_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_k_57_, lean_object* v_q_58_, lean_object* v_p_59_, lean_object* v_r_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lp_GRH_New_Columns_blockScaling___redArg(v_inst_53_, v_inst_56_, v_q_58_, v_p_59_, v_r_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Columns_blockScaling___boxed(lean_object* v_E_63_, lean_object* v_n_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_k_69_, lean_object* v_q_70_, lean_object* v_p_71_, lean_object* v_r_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_GRH_New_Columns_blockScaling(v_E_63_, v_n_64_, v_inst_65_, v_inst_66_, v_inst_67_, v_inst_68_, v_k_69_, v_q_70_, v_p_71_, v_r_72_, v_inst_73_);
lean_dec(v_k_69_);
lean_dec(v_inst_67_);
lean_dec_ref(v_inst_66_);
return v_res_74_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Divisibility_MarkedPrimes(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_ElementaryDivisorTheorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Divisibility_HeckeEdges(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_Divisibility_MarkedPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_ElementaryDivisorTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
