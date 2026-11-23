// Lean compiler output
// Module: Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrbitSg
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.HostOrbitCountSg public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_FrobeniusOrbits_sg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__0;
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1;
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__0, &lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__0_once, _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__0);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1, &lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1_once, _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb(lean_object* v_e_7_, lean_object* v_00_u03c4_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___y_13_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_fst_10_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v_x_9_, 1);
lean_inc(v_snd_11_);
lean_dec_ref(v_x_9_);
v___x_83_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_84_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1, &lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1_once, _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__1);
v___x_85_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_83_, v_fst_10_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v_fst_87_; 
v___x_86_ = lp_tree_Formalism_FrobeniusOrbits_sg(v_e_7_);
v_fst_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_fst_87_);
lean_dec_ref(v___x_86_);
v___y_13_ = v_fst_87_;
goto v___jp_12_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__2, &lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__2_once, _init_lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___closed__2);
v___y_13_ = v___x_88_;
goto v___jp_12_;
}
v___jp_12_:
{
lean_object* v_fst_14_; lean_object* v_fst_15_; lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_81_; 
v_fst_14_ = lean_ctor_get(v_00_u03c4_8_, 0);
lean_inc(v_fst_14_);
v_fst_15_ = lean_ctor_get(v___y_13_, 0);
lean_inc(v_fst_15_);
v_fst_16_ = lean_ctor_get(v_fst_14_, 0);
lean_inc(v_fst_16_);
v_snd_17_ = lean_ctor_get(v___y_13_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v___y_13_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v___y_13_, 0);
lean_dec(v_unused_82_);
v___x_19_ = v___y_13_;
v_isShared_20_ = v_isSharedCheck_81_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_snd_17_);
lean_dec(v___y_13_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_81_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v_snd_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_79_; 
v_snd_21_ = lean_ctor_get(v_fst_14_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_fst_14_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_fst_14_, 0);
lean_dec(v_unused_80_);
v___x_23_ = v_fst_14_;
v_isShared_24_ = v_isSharedCheck_79_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_snd_21_);
lean_dec(v_fst_14_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_79_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_snd_25_; lean_object* v_val_26_; lean_object* v_inv_27_; lean_object* v_val_28_; lean_object* v_inv_29_; lean_object* v_val_30_; lean_object* v_inv_31_; lean_object* v_val_32_; lean_object* v_inv_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_78_; 
v_snd_25_ = lean_ctor_get(v_00_u03c4_8_, 1);
lean_inc(v_snd_25_);
lean_dec_ref(v_00_u03c4_8_);
v_val_26_ = lean_ctor_get(v_fst_15_, 0);
lean_inc(v_val_26_);
v_inv_27_ = lean_ctor_get(v_fst_15_, 1);
lean_inc(v_inv_27_);
lean_dec(v_fst_15_);
v_val_28_ = lean_ctor_get(v_fst_16_, 0);
lean_inc(v_val_28_);
v_inv_29_ = lean_ctor_get(v_fst_16_, 1);
lean_inc(v_inv_29_);
lean_dec(v_fst_16_);
v_val_30_ = lean_ctor_get(v_snd_17_, 0);
lean_inc(v_val_30_);
v_inv_31_ = lean_ctor_get(v_snd_17_, 1);
lean_inc(v_inv_31_);
lean_dec(v_snd_17_);
v_val_32_ = lean_ctor_get(v_snd_21_, 0);
v_inv_33_ = lean_ctor_get(v_snd_21_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_snd_21_);
if (v_isSharedCheck_78_ == 0)
{
v___x_35_ = v_snd_21_;
v_isShared_36_ = v_isSharedCheck_78_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_inv_33_);
lean_inc(v_val_32_);
lean_dec(v_snd_21_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_78_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v_toSemiring_41_; lean_object* v_toMonoid_42_; lean_object* v___x_43_; lean_object* v_toMul_44_; lean_object* v_val_45_; lean_object* v_inv_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_77_; 
v___x_37_ = lean_unsigned_to_nat(2u);
v___x_38_ = lean_nat_add(v_e_7_, v___x_37_);
v___x_39_ = lean_nat_pow(v___x_37_, v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = lp_mathlib_ZMod_commRing(v___x_39_);
v_toSemiring_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc_ref(v_toSemiring_41_);
lean_dec_ref(v___x_40_);
v_toMonoid_42_ = lean_ctor_get(v_toSemiring_41_, 1);
lean_inc_ref(v_toMonoid_42_);
lean_dec_ref(v_toSemiring_41_);
v___x_43_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_42_);
lean_dec_ref(v_toMonoid_42_);
v_toMul_44_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_toMul_44_);
lean_dec_ref(v___x_43_);
v_val_45_ = lean_ctor_get(v_snd_11_, 0);
v_inv_46_ = lean_ctor_get(v_snd_11_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_snd_11_);
if (v_isSharedCheck_77_ == 0)
{
v___x_48_ = v_snd_11_;
v_isShared_49_ = v_isSharedCheck_77_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_inv_46_);
lean_inc(v_val_45_);
lean_dec(v_snd_11_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_77_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v_val_50_; lean_object* v_inv_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_76_; 
v_val_50_ = lean_ctor_get(v_snd_25_, 0);
v_inv_51_ = lean_ctor_get(v_snd_25_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_snd_25_);
if (v_isSharedCheck_76_ == 0)
{
v___x_53_ = v_snd_25_;
v_isShared_54_ = v_isSharedCheck_76_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_inv_51_);
lean_inc(v_val_50_);
lean_dec(v_snd_25_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_76_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_55_ = lean_int_mul(v_val_26_, v_val_28_);
lean_dec(v_val_28_);
lean_dec(v_val_26_);
v___x_56_ = lean_int_mul(v_inv_29_, v_inv_27_);
lean_dec(v_inv_27_);
lean_dec(v_inv_29_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_56_);
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_56_);
v___x_58_ = v_reuseFailAlloc_75_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_59_ = lean_int_mul(v_val_30_, v_val_32_);
lean_dec(v_val_32_);
lean_dec(v_val_30_);
v___x_60_ = lean_int_mul(v_inv_33_, v_inv_31_);
lean_dec(v_inv_31_);
lean_dec(v_inv_33_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v___x_60_);
lean_ctor_set(v___x_48_, 0, v___x_59_);
v___x_62_ = v___x_48_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_74_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_64_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_62_);
lean_ctor_set(v___x_23_, 0, v___x_58_);
v___x_64_ = v___x_23_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_73_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
lean_inc(v_toMul_44_);
v___x_65_ = lean_apply_2(v_toMul_44_, v_val_45_, v_val_50_);
v___x_66_ = lean_apply_2(v_toMul_44_, v_inv_51_, v_inv_46_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___x_66_);
lean_ctor_set(v___x_35_, 0, v___x_65_);
v___x_68_ = v___x_35_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_72_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_70_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v___x_68_);
lean_ctor_set(v___x_19_, 0, v___x_64_);
v___x_70_ = v___x_19_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
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
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb___boxed(lean_object* v_e_89_, lean_object* v_00_u03c4_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_tree_Formalism_FrobeniusOrbits_OrbitSg_emb(v_e_89_, v_00_u03c4_90_, v_x_91_);
lean_dec(v_e_89_);
return v_res_92_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostOrbitCountSg(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_HostOrbitCountSg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
