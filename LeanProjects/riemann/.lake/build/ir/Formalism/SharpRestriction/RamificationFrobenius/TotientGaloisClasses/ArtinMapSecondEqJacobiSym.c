// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator public import Formalism.FrobeniusOrbits.HostCorollaries
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toMonoidWithZero___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
uint8_t lp_mathlib_Fintype_IsSquare_decidablePred___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_ZMod_unitsMap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_prod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0;
static lean_once_cell_t lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__1;
static lean_once_cell_t lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sgnN___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sgnN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___closed__0 = (const lean_object*)&lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0);
v___x_4_ = lean_int_neg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_to_int(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0(lean_object* v_p_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_toSemiring_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_toMul_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_toZero_18_; uint8_t v___x_19_; 
lean_inc(v_p_7_);
v___x_9_ = lp_mathlib_ZMod_instField___redArg(v_p_7_);
v___x_10_ = lp_mathlib_Field_toSemifield___redArg(v___x_9_);
lean_dec_ref(v___x_9_);
v___x_11_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_10_);
v_toSemiring_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_toSemiring_12_);
lean_dec_ref(v___x_11_);
v___x_13_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_12_);
v___x_14_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_12_);
v_toMul_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_toMul_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(v___x_13_);
v___x_17_ = lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(v___x_16_);
v_toZero_18_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_toZero_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lp_mathlib_ZMod_decidableEq(v_p_7_, v_a_8_, v_toZero_18_);
lean_dec(v_toZero_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
lean_inc(v_p_7_);
v___x_20_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_20_, 0, v_p_7_);
v___x_21_ = lp_mathlib_ZMod_fintype___redArg(v_p_7_);
lean_dec(v_p_7_);
v___x_22_ = lp_mathlib_Fintype_IsSquare_decidablePred___redArg(v_toMul_15_, v___x_21_, v___x_20_, v_a_8_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__1, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__1_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__1);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__0);
return v___x_24_;
}
}
else
{
lean_object* v___x_25_; 
lean_dec(v_toMul_15_);
lean_dec(v_a_8_);
lean_dec(v_p_7_);
v___x_25_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__2, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__2_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0___closed__2);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0___lam__0(lean_object* v_p_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0_spec__0(v_p_26_, v___y_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0(lean_object* v_p_29_){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = lean_alloc_closure((void*)(lp_tree_quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_30_, 0, v_p_29_);
return v___f_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0(lean_object* v_f_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_1(v_f_31_, v___y_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg(lean_object* v_f_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = lean_alloc_closure((void*)(lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0), 2, 1);
lean_closure_set(v___f_35_, 0, v_f_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3___lam__0(lean_object* v_f_36_, lean_object* v_u_37_){
_start:
{
lean_object* v_val_38_; lean_object* v_inv_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_48_; 
v_val_38_ = lean_ctor_get(v_u_37_, 0);
v_inv_39_ = lean_ctor_get(v_u_37_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_u_37_);
if (v_isSharedCheck_48_ == 0)
{
v___x_41_ = v_u_37_;
v_isShared_42_ = v_isSharedCheck_48_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_inv_39_);
lean_inc(v_val_38_);
lean_dec(v_u_37_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_48_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
lean_inc_ref(v_f_36_);
v___x_43_ = lean_apply_1(v_f_36_, v_val_38_);
v___x_44_ = lean_apply_1(v_f_36_, v_inv_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_44_);
lean_ctor_set(v___x_41_, 0, v___x_43_);
v___x_46_ = v___x_41_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3(lean_object* v_p_49_, lean_object* v_f_50_){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_51_, 0, v_f_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3___boxed(lean_object* v_p_52_, lean_object* v_f_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3(v_p_52_, v_f_53_);
lean_dec(v_p_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1(lean_object* v_p_55_, lean_object* v_00_u03c7_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; 
v___f_57_ = lean_alloc_closure((void*)(lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0), 2, 1);
lean_closure_set(v___f_57_, 0, v_00_u03c7_56_);
v___f_58_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_58_, 0, v___f_57_);
return v___f_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1___boxed(lean_object* v_p_59_, lean_object* v_00_u03c7_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1(v_p_59_, v_00_u03c7_60_);
lean_dec(v_p_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sgnN___redArg(lean_object* v_p_62_, lean_object* v_N_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___f_67_; 
lean_inc(v_p_62_);
v___f_64_ = lean_alloc_closure((void*)(lp_tree_quadraticChar___at___00Formalism_HC_D7_sgnN_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_64_, 0, v_p_62_);
v___x_65_ = lp_tree_MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1(v_p_62_, v___f_64_);
v___x_66_ = lp_mathlib_ZMod_unitsMap___redArg(v_p_62_, v_N_63_);
v___f_67_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_67_, 0, v___x_66_);
lean_closure_set(v___f_67_, 1, v___x_65_);
return v___f_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sgnN(lean_object* v_p_68_, lean_object* v_N_69_, lean_object* v_hp_70_, lean_object* v_h_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_tree_Formalism_HC_D7_sgnN___redArg(v_p_68_, v_N_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3(lean_object* v_p_73_, lean_object* v_inst_74_, lean_object* v_f_75_){
_start:
{
lean_object* v___f_76_; 
v___f_76_ = lean_alloc_closure((void*)(lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0), 2, 1);
lean_closure_set(v___f_76_, 0, v_f_75_);
return v___f_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___boxed(lean_object* v_p_77_, lean_object* v_inst_78_, lean_object* v_f_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3(v_p_77_, v_inst_78_, v_f_79_);
lean_dec(v_p_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___redArg(lean_object* v_p_81_, lean_object* v_f_82_){
_start:
{
lean_object* v___f_83_; 
v___f_83_ = lean_alloc_closure((void*)(lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0), 2, 1);
lean_closure_set(v___f_83_, 0, v_f_82_);
return v___f_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___redArg___boxed(lean_object* v_p_84_, lean_object* v_f_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___redArg(v_p_84_, v_f_85_);
lean_dec(v_p_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2(lean_object* v_p_87_, lean_object* v_inst_88_, lean_object* v_f_89_){
_start:
{
lean_object* v___f_90_; 
v___f_90_ = lean_alloc_closure((void*)(lp_tree_MulHomClass_toMulHom___at___00MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2_spec__3___redArg___lam__0), 2, 1);
lean_closure_set(v___f_90_, 0, v_f_89_);
return v___f_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2___boxed(lean_object* v_p_91_, lean_object* v_inst_92_, lean_object* v_f_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_tree_MonoidHomClass_toMonoidHom___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__2(v_p_91_, v_inst_92_, v_f_93_);
lean_dec(v_p_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___redArg(lean_object* v_f_95_){
_start:
{
lean_inc_ref(v_f_95_);
return v_f_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___redArg(v_f_96_);
lean_dec_ref(v_f_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5(lean_object* v_p_98_, lean_object* v_f_99_, lean_object* v_map__mul_100_){
_start:
{
lean_inc_ref(v_f_99_);
return v_f_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5___boxed(lean_object* v_p_101_, lean_object* v_f_102_, lean_object* v_map__mul_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00MulChar_toUnitHom___at___00Formalism_HC_D7_sgnN_spec__1_spec__3_spec__5(v_p_101_, v_f_102_, v_map__mul_103_);
lean_dec_ref(v_f_102_);
lean_dec(v_p_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg___lam__0(lean_object* v_f_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_1(v_f_105_, v___y_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg___lam__1(lean_object* v_g_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_apply_1(v_g_108_, v___y_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg(lean_object* v_f_111_, lean_object* v_g_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v___f_113_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_113_, 0, v_f_111_);
v___f_114_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg___lam__1), 2, 1);
lean_closure_set(v___f_114_, 0, v_g_112_);
v___x_115_ = lean_alloc_closure((void*)(lp_mathlib_Function_prod), 6, 5);
lean_closure_set(v___x_115_, 0, lean_box(0));
lean_closure_set(v___x_115_, 1, lean_box(0));
lean_closure_set(v___x_115_, 2, lean_box(0));
lean_closure_set(v___x_115_, 3, v___f_113_);
lean_closure_set(v___x_115_, 4, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0(lean_object* v___x_116_, lean_object* v_f_117_, lean_object* v_g_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg(v_f_117_, v_g_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___boxed(lean_object* v___x_120_, lean_object* v_f_121_, lean_object* v_g_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0(v___x_120_, v_f_121_, v_g_122_);
lean_dec(v___x_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg___lam__0(lean_object* v_f_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_apply_1(v_f_124_, v___y_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg___lam__1(lean_object* v_g_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_apply_1(v_g_127_, v___y_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg(lean_object* v_f_130_, lean_object* v_g_131_){
_start:
{
lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v___f_132_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_132_, 0, v_f_130_);
v___f_133_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg___lam__1), 2, 1);
lean_closure_set(v___f_133_, 0, v_g_131_);
v___x_134_ = lean_alloc_closure((void*)(lp_mathlib_Function_prod), 6, 5);
lean_closure_set(v___x_134_, 0, lean_box(0));
lean_closure_set(v___x_134_, 1, lean_box(0));
lean_closure_set(v___x_134_, 2, lean_box(0));
lean_closure_set(v___x_134_, 3, v___f_132_);
lean_closure_set(v___x_134_, 4, v___f_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2(lean_object* v___x_135_, lean_object* v___x_136_, lean_object* v___x_137_, lean_object* v_f_138_, lean_object* v_g_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg(v_f_138_, v_g_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___boxed(lean_object* v___x_141_, lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_f_144_, lean_object* v_g_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2(v___x_141_, v___x_142_, v___x_143_, v_f_144_, v_g_145_);
lean_dec(v___x_142_);
lean_dec(v___x_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___lam__0(lean_object* v___y_147_){
_start:
{
lean_inc_ref(v___y_147_);
return v___y_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___lam__0___boxed(lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___lam__0(v___y_148_);
lean_dec_ref(v___y_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg(lean_object* v___x_151_, lean_object* v_N_152_){
_start:
{
lean_object* v___f_153_; 
v___f_153_ = ((lean_object*)(lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___closed__0));
return v___f_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___boxed(lean_object* v___x_154_, lean_object* v_N_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg(v___x_154_, v_N_155_);
lean_dec(v___x_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0___redArg(lean_object* v_q_157_, lean_object* v_d_158_, lean_object* v_e_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___x_171_; 
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_nat_add(v_e_159_, v___x_160_);
v___x_162_ = lean_nat_pow(v___x_160_, v___x_161_);
lean_dec(v___x_161_);
v___x_163_ = lean_nat_mul(v___x_162_, v_q_157_);
v___x_164_ = lean_nat_mul(v___x_163_, v_d_158_);
lean_dec(v___x_163_);
lean_inc_n(v___x_164_, 2);
v___x_165_ = lp_tree_Formalism_HC_D7_sgnN___redArg(v_q_157_, v___x_164_);
v___x_166_ = lp_tree_Formalism_HC_D7_sgnN___redArg(v_d_158_, v___x_164_);
v___x_167_ = lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__0___redArg(v___x_165_, v___x_166_);
v___f_168_ = ((lean_object*)(lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___closed__0));
v___x_169_ = lp_mathlib_ZMod_unitsMap___redArg(v___x_162_, v___x_164_);
v___f_170_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_170_, 0, v___x_169_);
lean_closure_set(v___f_170_, 1, v___f_168_);
v___x_171_ = lp_tree_MonoidHom_prod___at___00Formalism_HC_D7_art0_spec__2___redArg(v___x_167_, v___f_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0___redArg___boxed(lean_object* v_q_172_, lean_object* v_d_173_, lean_object* v_e_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = lp_tree_Formalism_HC_D7_art0___redArg(v_q_172_, v_d_173_, v_e_174_);
lean_dec(v_e_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0(lean_object* v_q_176_, lean_object* v_d_177_, lean_object* v_e_178_, lean_object* v_hH_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lp_tree_Formalism_HC_D7_art0___redArg(v_q_176_, v_d_177_, v_e_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_art0___boxed(lean_object* v_q_181_, lean_object* v_d_182_, lean_object* v_e_183_, lean_object* v_hH_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = lp_tree_Formalism_HC_D7_art0(v_q_181_, v_d_182_, v_e_183_, v_hH_184_);
lean_dec(v_e_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___redArg(lean_object* v_f_186_){
_start:
{
lean_inc(v_f_186_);
return v_f_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___redArg___boxed(lean_object* v_f_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___redArg(v_f_187_);
lean_dec(v_f_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1(lean_object* v___x_189_, lean_object* v_N_190_, lean_object* v_f_191_, lean_object* v_map__mul_192_){
_start:
{
lean_inc(v_f_191_);
return v_f_191_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1___boxed(lean_object* v___x_193_, lean_object* v_N_194_, lean_object* v_f_195_, lean_object* v_map__mul_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lp_tree_MonoidHom_mk_x27___at___00QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1_spec__1(v___x_193_, v_N_194_, v_f_195_, v_map__mul_196_);
lean_dec(v_f_195_);
lean_dec(v___x_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1(lean_object* v___x_198_, lean_object* v_N_199_, lean_object* v_nN_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = ((lean_object*)(lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___redArg___closed__0));
return v___f_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1___boxed(lean_object* v___x_202_, lean_object* v_N_203_, lean_object* v_nN_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = lp_tree_QuotientGroup_mk_x27___at___00Formalism_HC_D7_art0_spec__1(v___x_202_, v_N_203_, v_nN_204_);
lean_dec(v___x_202_);
return v_res_205_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
