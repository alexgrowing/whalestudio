// Lean compiler output
// Module: Formalism.FrobeniusOrbits.HostOrbitsPlaces
// Imports: public import Init public meta import Init public import Formalism.FrobeniusOrbits.Statement
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_tree_Formalism_FrobeniusOrbits_cc(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Formalism_FrobeniusOrbits_placeOf_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Formalism_FrobeniusOrbits_placeOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__0;
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_placeOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_placeOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Formalism_FrobeniusOrbits_placeOf_spec__0___redArg(lean_object* v_f_1_, lean_object* v_q_u2081_2_, lean_object* v_q_u2082_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_f_1_, v_q_u2081_2_, v_q_u2082_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Formalism_FrobeniusOrbits_placeOf_spec__0(lean_object* v_f_5_, lean_object* v_h_6_, lean_object* v_q_u2081_7_, lean_object* v_q_u2082_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_f_5_, v_q_u2081_7_, v_q_u2082_8_);
return v___x_9_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_to_int(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__1(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__0, &lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__0_once, _init_lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__0);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_placeOf(lean_object* v_e_14_, lean_object* v_g_15_){
_start:
{
lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_fst_16_ = lean_ctor_get(v_g_15_, 0);
v_snd_17_ = lean_ctor_get(v_g_15_, 1);
lean_inc(v_snd_17_);
v_fst_18_ = lean_ctor_get(v_fst_16_, 0);
v_snd_19_ = lean_ctor_get(v_fst_16_, 1);
lean_inc_n(v_snd_19_, 2);
v___x_20_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_21_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__1, &lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__1_once, _init_lp_tree_Formalism_FrobeniusOrbits_placeOf___closed__1);
v___x_22_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_20_, v_snd_19_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_toSemiring_27_; lean_object* v_toMonoid_28_; lean_object* v___x_29_; lean_object* v_fst_30_; lean_object* v_fst_31_; lean_object* v_snd_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_89_; 
lean_inc(v_fst_18_);
lean_dec_ref(v_g_15_);
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lean_nat_add(v_e_14_, v___x_23_);
v___x_25_ = lean_nat_pow(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
v___x_26_ = lp_mathlib_ZMod_commRing(v___x_25_);
v_toSemiring_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc_ref(v_toSemiring_27_);
lean_dec_ref(v___x_26_);
v_toMonoid_28_ = lean_ctor_get(v_toSemiring_27_, 1);
lean_inc_ref(v_toMonoid_28_);
lean_dec_ref(v_toSemiring_27_);
v___x_29_ = lp_tree_Formalism_FrobeniusOrbits_cc(v_e_14_);
v_fst_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_fst_30_);
v_fst_31_ = lean_ctor_get(v_fst_30_, 0);
v_snd_32_ = lean_ctor_get(v_fst_30_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_fst_30_);
if (v_isSharedCheck_89_ == 0)
{
v___x_34_ = v_fst_30_;
v_isShared_35_ = v_isSharedCheck_89_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_snd_32_);
lean_inc(v_fst_31_);
lean_dec(v_fst_30_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_89_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v_snd_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_87_; 
v_snd_36_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_29_, 0);
lean_dec(v_unused_88_);
v___x_38_ = v___x_29_;
v_isShared_39_ = v_isSharedCheck_87_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_snd_36_);
lean_dec(v___x_29_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_87_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v_val_40_; lean_object* v_inv_41_; lean_object* v_val_42_; lean_object* v_inv_43_; lean_object* v_val_44_; lean_object* v_inv_45_; lean_object* v_val_46_; lean_object* v_inv_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_86_; 
v_val_40_ = lean_ctor_get(v_fst_31_, 0);
lean_inc(v_val_40_);
v_inv_41_ = lean_ctor_get(v_fst_31_, 1);
lean_inc(v_inv_41_);
lean_dec(v_fst_31_);
v_val_42_ = lean_ctor_get(v_fst_18_, 0);
lean_inc(v_val_42_);
v_inv_43_ = lean_ctor_get(v_fst_18_, 1);
lean_inc(v_inv_43_);
lean_dec(v_fst_18_);
v_val_44_ = lean_ctor_get(v_snd_32_, 0);
lean_inc(v_val_44_);
v_inv_45_ = lean_ctor_get(v_snd_32_, 1);
lean_inc(v_inv_45_);
lean_dec(v_snd_32_);
v_val_46_ = lean_ctor_get(v_snd_19_, 0);
v_inv_47_ = lean_ctor_get(v_snd_19_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_snd_19_);
if (v_isSharedCheck_86_ == 0)
{
v___x_49_ = v_snd_19_;
v_isShared_50_ = v_isSharedCheck_86_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_inv_47_);
lean_inc(v_val_46_);
lean_dec(v_snd_19_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_86_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v_toMul_52_; lean_object* v_val_53_; lean_object* v_inv_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_85_; 
v___x_51_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_28_);
lean_dec_ref(v_toMonoid_28_);
v_toMul_52_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_toMul_52_);
lean_dec_ref(v___x_51_);
v_val_53_ = lean_ctor_get(v_snd_36_, 0);
v_inv_54_ = lean_ctor_get(v_snd_36_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_snd_36_);
if (v_isSharedCheck_85_ == 0)
{
v___x_56_ = v_snd_36_;
v_isShared_57_ = v_isSharedCheck_85_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_inv_54_);
lean_inc(v_val_53_);
lean_dec(v_snd_36_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_85_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_val_58_; lean_object* v_inv_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_84_; 
v_val_58_ = lean_ctor_get(v_snd_17_, 0);
v_inv_59_ = lean_ctor_get(v_snd_17_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_snd_17_);
if (v_isSharedCheck_84_ == 0)
{
v___x_61_ = v_snd_17_;
v_isShared_62_ = v_isSharedCheck_84_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_inv_59_);
lean_inc(v_val_58_);
lean_dec(v_snd_17_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_84_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_63_ = lean_int_mul(v_val_40_, v_val_42_);
lean_dec(v_val_42_);
lean_dec(v_val_40_);
v___x_64_ = lean_int_mul(v_inv_43_, v_inv_41_);
lean_dec(v_inv_41_);
lean_dec(v_inv_43_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_64_);
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_66_ = v___x_61_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_83_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_67_ = lean_int_mul(v_val_44_, v_val_46_);
lean_dec(v_val_46_);
lean_dec(v_val_44_);
v___x_68_ = lean_int_mul(v_inv_47_, v_inv_45_);
lean_dec(v_inv_45_);
lean_dec(v_inv_47_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___x_68_);
lean_ctor_set(v___x_56_, 0, v___x_67_);
v___x_70_ = v___x_56_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_82_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_70_);
lean_ctor_set(v___x_34_, 0, v___x_66_);
v___x_72_ = v___x_34_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_81_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
lean_inc(v_toMul_52_);
v___x_73_ = lean_apply_2(v_toMul_52_, v_val_53_, v_val_58_);
v___x_74_ = lean_apply_2(v_toMul_52_, v_inv_59_, v_inv_54_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v___x_74_);
lean_ctor_set(v___x_49_, 0, v___x_73_);
v___x_76_ = v___x_49_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v___x_74_);
v___x_76_ = v_reuseFailAlloc_80_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_78_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v___x_76_);
lean_ctor_set(v___x_38_, 0, v___x_72_);
v___x_78_ = v___x_38_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v_snd_19_);
lean_dec(v_snd_17_);
return v_g_15_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_placeOf___boxed(lean_object* v_e_90_, lean_object* v_g_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_tree_Formalism_FrobeniusOrbits_placeOf(v_e_90_, v_g_91_);
lean_dec(v_e_90_);
return v_res_92_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostOrbitsPlaces(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
