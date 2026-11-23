// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_primeFactors(lean_object*);
lean_object* lp_mathlib_Multiset_erase___at___00Finset_erase___at___00Multiset_bell_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_SM___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_SM___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_HC_HType_SM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_HC_HType_SM___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HC_HType_SM___closed__0 = (const lean_object*)&lp_tree_Formalism_HC_HType_SM___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_SM(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__1___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_HC_HType_P___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_HC_HType_P___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HC_HType_P___closed__0 = (const lean_object*)&lp_tree_Formalism_HC_HType_P___closed__0_value;
static const lean_closure_object lp_tree_Formalism_HC_HType_P___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_HC_HType_P___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HC_HType_P___closed__1 = (const lean_object*)&lp_tree_Formalism_HC_HType_P___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_SM___lam__0(lean_object* v_00_u03c8_1_){
_start:
{
lean_object* v_N_2_; 
v_N_2_ = lean_ctor_get(v_00_u03c8_1_, 0);
lean_inc(v_N_2_);
return v_N_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_SM___lam__0___boxed(lean_object* v_00_u03c8_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_tree_Formalism_HC_HType_SM___lam__0(v_00_u03c8_3_);
lean_dec_ref(v_00_u03c8_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_SM(lean_object* v_T_6_){
_start:
{
lean_object* v_toKSet_7_; lean_object* v_P0_8_; lean_object* v_KEPT_9_; lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_toKSet_7_ = lean_ctor_get(v_T_6_, 0);
lean_inc_ref(v_toKSet_7_);
v_P0_8_ = lean_ctor_get(v_T_6_, 3);
lean_inc(v_P0_8_);
lean_dec_ref(v_T_6_);
v_KEPT_9_ = lean_ctor_get(v_toKSet_7_, 0);
lean_inc(v_KEPT_9_);
lean_dec_ref(v_toKSet_7_);
v___f_10_ = ((lean_object*)(lp_tree_Formalism_HC_HType_SM___closed__0));
v___x_11_ = lean_unsigned_to_nat(2u);
v___x_12_ = lean_nat_mul(v___x_11_, v_P0_8_);
lean_dec(v_P0_8_);
v___x_13_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v_KEPT_9_, v___f_10_);
v___x_14_ = lean_nat_mul(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_12_);
v___x_15_ = lp_mathlib_Nat_primeFactors(v___x_14_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__0(lean_object* v_l_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_sub(v_l_16_, v___x_17_);
v___x_19_ = lean_nat_mul(v_l_16_, v___x_18_);
lean_dec(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__0___boxed(lean_object* v_l_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_HC_HType_P___lam__0(v_l_20_);
lean_dec(v_l_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__1(lean_object* v_p_22_){
_start:
{
lean_inc(v_p_22_);
return v_p_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P___lam__1___boxed(lean_object* v_p_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_HC_HType_P___lam__1(v_p_23_);
lean_dec(v_p_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_P(lean_object* v_T_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___f_28_ = ((lean_object*)(lp_tree_Formalism_HC_HType_P___closed__0));
v___f_29_ = ((lean_object*)(lp_tree_Formalism_HC_HType_P___closed__1));
v___x_30_ = lp_tree_Formalism_HC_HType_SM(v_T_27_);
v___x_31_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_30_, v___f_28_);
v___x_32_ = lp_mathlib_Nat_primeFactors(v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_unsigned_to_nat(2u);
v___x_34_ = lp_mathlib_Multiset_erase___at___00Finset_erase___at___00Multiset_bell_spec__3_spec__6(v___x_32_, v___x_33_);
v___x_35_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_34_, v___f_29_);
return v___x_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
