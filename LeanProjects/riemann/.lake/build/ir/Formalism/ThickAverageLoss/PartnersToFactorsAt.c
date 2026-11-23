// Lean compiler output
// Module: Formalism.ThickAverageLoss.PartnersToFactorsAt
// Imports: public import Init public meta import Init public import Formalism.ThickAverageLoss.Statement public import Formalism.CorankShare.StatementFR public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_D5_sgn2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_sgn2___closed__0;
static lean_once_cell_t lp_tree_Formalism_D5_sgn2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_sgn2___closed__1;
static lean_once_cell_t lp_tree_Formalism_D5_sgn2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_sgn2___closed__2;
static lean_once_cell_t lp_tree_Formalism_D5_sgn2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_sgn2___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_sgn2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_sgn2___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_D5_cconj___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_cconj___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_topPl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_topPl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_thickPl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_thickPl(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_D5_PhiSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_D5_PhiSet___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_D5_PhiSet___redArg___closed__0_value;
static lean_once_cell_t lp_tree_Formalism_D5_PhiSet___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_PhiSet___redArg___closed__1;
static lean_once_cell_t lp_tree_Formalism_D5_PhiSet___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_D5_PhiSet___redArg___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_PhiSet___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_PhiSet(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_ZMod_decidableEq___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___closed__0_value;
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___closed__0_value;
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_D5_sgn2___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_ZMod_instField___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_sgn2___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__0, &lp_tree_Formalism_D5_sgn2___closed__0_once, _init_lp_tree_Formalism_D5_sgn2___closed__0);
v___x_4_ = lp_mathlib_Field_toSemifield___redArg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_sgn2___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__1, &lp_tree_Formalism_D5_sgn2___closed__1_once, _init_lp_tree_Formalism_D5_sgn2___closed__1);
v___x_6_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_sgn2___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___f_8_; 
v___x_7_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_8_, 0, v___x_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_sgn2(lean_object* v_e_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_toSemiring_12_; lean_object* v___x_13_; lean_object* v_toZero_14_; uint8_t v___x_15_; 
v___x_10_ = lean_unsigned_to_nat(2u);
v___x_11_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__2, &lp_tree_Formalism_D5_sgn2___closed__2_once, _init_lp_tree_Formalism_D5_sgn2___closed__2);
v_toSemiring_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_toSemiring_12_);
v___x_13_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_12_);
v_toZero_14_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_toZero_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lp_mathlib_ZMod_decidableEq(v___x_10_, v_e_9_, v_toZero_14_);
lean_dec(v_toZero_14_);
if (v___x_15_ == 0)
{
lean_object* v___f_16_; 
v___f_16_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__3, &lp_tree_Formalism_D5_sgn2___closed__3_once, _init_lp_tree_Formalism_D5_sgn2___closed__3);
return v___f_16_;
}
else
{
lean_object* v___x_17_; 
v___x_17_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_sgn2___boxed(lean_object* v_e_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_D5_sgn2(v_e_18_);
lean_dec(v_e_18_);
return v_res_19_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(lean_object* v_g_20_){
_start:
{
lean_object* v_fst_21_; lean_object* v_fst_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toSemiring_25_; lean_object* v___x_26_; lean_object* v_toZero_27_; uint8_t v___x_28_; 
v_fst_21_ = lean_ctor_get(v_g_20_, 0);
v_fst_22_ = lean_ctor_get(v_fst_21_, 0);
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__2, &lp_tree_Formalism_D5_sgn2___closed__2_once, _init_lp_tree_Formalism_D5_sgn2___closed__2);
v_toSemiring_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_toSemiring_25_);
v___x_26_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_25_);
v_toZero_27_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_toZero_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = lp_mathlib_ZMod_decidableEq(v___x_23_, v_fst_22_, v_toZero_27_);
lean_dec(v_toZero_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg___boxed(lean_object* v_g_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(v_g_29_);
lean_dec_ref(v_g_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1(lean_object* v_H_32_, lean_object* v_g_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(v_g_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___boxed(lean_object* v_H_35_, lean_object* v_g_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1(v_H_35_, v_g_36_);
lean_dec_ref(v_g_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___redArg(lean_object* v_g_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(v_g_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___redArg___boxed(lean_object* v_g_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___redArg(v_g_41_);
lean_dec_ref(v_g_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi(lean_object* v_H_44_, lean_object* v_g_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(v_g_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___boxed(lean_object* v_H_47_, lean_object* v_g_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi(v_H_47_, v_g_48_);
lean_dec_ref(v_g_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_cconj___redArg___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__0, &lp_tree_Formalism_D5_sgn2___closed__0_once, _init_lp_tree_Formalism_D5_sgn2___closed__0);
v___x_52_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj___redArg(lean_object* v_inst_53_){
_start:
{
lean_object* v___x_54_; lean_object* v_toRing_55_; lean_object* v___x_56_; lean_object* v_toAddMonoidWithOne_57_; lean_object* v_toOne_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_toZero_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v___x_54_ = lean_obj_once(&lp_tree_Formalism_D5_cconj___redArg___closed__0, &lp_tree_Formalism_D5_cconj___redArg___closed__0_once, _init_lp_tree_Formalism_D5_cconj___redArg___closed__0);
v_toRing_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_toRing_55_);
v___x_56_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_55_);
v_toAddMonoidWithOne_57_ = lean_ctor_get(v___x_56_, 1);
lean_inc_ref(v_toAddMonoidWithOne_57_);
lean_dec_ref(v___x_56_);
v_toOne_58_ = lean_ctor_get(v_toAddMonoidWithOne_57_, 2);
lean_inc_n(v_toOne_58_, 2);
lean_dec_ref(v_toAddMonoidWithOne_57_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_toOne_58_);
lean_ctor_set(v___x_59_, 1, v_toOne_58_);
v___x_60_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_inst_53_);
v_toZero_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_68_ == 0)
{
lean_object* v_unused_69_; 
v_unused_69_ = lean_ctor_get(v___x_60_, 1);
lean_dec(v_unused_69_);
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_toZero_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_toZero_61_);
lean_ctor_set(v___x_63_, 0, v___x_59_);
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_toZero_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj___redArg___boxed(lean_object* v_inst_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_D5_cconj___redArg(v_inst_70_);
lean_dec_ref(v_inst_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj(lean_object* v_H_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_D5_cconj___redArg(v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_cconj___boxed(lean_object* v_H_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_D5_cconj(v_H_75_, v_inst_76_);
lean_dec_ref(v_inst_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_topPl___redArg(lean_object* v_t_78_){
_start:
{
lean_object* v___x_79_; lean_object* v_toSemiring_80_; lean_object* v___x_81_; lean_object* v_toZero_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
v___x_79_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__2, &lp_tree_Formalism_D5_sgn2___closed__2_once, _init_lp_tree_Formalism_D5_sgn2___closed__2);
v_toSemiring_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_toSemiring_80_);
v___x_81_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_80_);
v_toZero_82_ = lean_ctor_get(v___x_81_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_91_);
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_toZero_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
lean_inc(v_toZero_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v_toZero_82_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_toZero_82_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_toZero_82_);
v___x_87_ = v_reuseFailAlloc_89_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_t_78_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_topPl(lean_object* v_H_92_, lean_object* v_t_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_tree_Formalism_D5_topPl___redArg(v_t_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_thickPl___redArg(lean_object* v_t_95_){
_start:
{
lean_object* v___x_96_; lean_object* v_toSemiring_97_; lean_object* v___x_98_; lean_object* v_toZero_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_112_; 
v___x_96_ = lean_obj_once(&lp_tree_Formalism_D5_sgn2___closed__2, &lp_tree_Formalism_D5_sgn2___closed__2_once, _init_lp_tree_Formalism_D5_sgn2___closed__2);
v_toSemiring_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_toSemiring_97_);
v___x_98_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_97_);
v_toZero_99_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v___x_98_, 0);
lean_dec(v_unused_113_);
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_112_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_toZero_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_112_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v_toRing_104_; lean_object* v___x_105_; lean_object* v_toAddMonoidWithOne_106_; lean_object* v_toOne_107_; lean_object* v___x_109_; 
v___x_103_ = lean_obj_once(&lp_tree_Formalism_D5_cconj___redArg___closed__0, &lp_tree_Formalism_D5_cconj___redArg___closed__0_once, _init_lp_tree_Formalism_D5_cconj___redArg___closed__0);
v_toRing_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_toRing_104_);
v___x_105_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_104_);
v_toAddMonoidWithOne_106_ = lean_ctor_get(v___x_105_, 1);
lean_inc_ref(v_toAddMonoidWithOne_106_);
lean_dec_ref(v___x_105_);
v_toOne_107_ = lean_ctor_get(v_toAddMonoidWithOne_106_, 2);
lean_inc(v_toOne_107_);
lean_dec_ref(v_toAddMonoidWithOne_106_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_toOne_107_);
lean_ctor_set(v___x_101_, 0, v_toZero_99_);
v___x_109_ = v___x_101_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_toZero_99_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_toOne_107_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v_t_95_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_thickPl(lean_object* v_H_114_, lean_object* v_t_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lp_tree_Formalism_D5_thickPl___redArg(v_t_115_);
return v___x_116_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_PhiSet___redArg___closed__1(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = lp_mathlib_ZMod_fintype___redArg(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_lp_tree_Formalism_D5_PhiSet___redArg___closed__2(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&lp_tree_Formalism_D5_PhiSet___redArg___closed__1, &lp_tree_Formalism_D5_PhiSet___redArg___closed__1_once, _init_lp_tree_Formalism_D5_PhiSet___redArg___closed__1);
v___x_121_ = lp_mathlib_Multiset_product___redArg(v___x_120_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_PhiSet___redArg(lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(lp_tree_Formalism_D5_PhiSet___redArg___closed__0));
v___x_124_ = lean_obj_once(&lp_tree_Formalism_D5_PhiSet___redArg___closed__2, &lp_tree_Formalism_D5_PhiSet___redArg___closed__2_once, _init_lp_tree_Formalism_D5_PhiSet___redArg___closed__2);
v___x_125_ = lp_mathlib_Multiset_product___redArg(v___x_124_, v_inst_122_);
v___x_126_ = lp_mathlib_Multiset_filter___redArg(v___x_123_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_PhiSet(lean_object* v_H_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_tree_Formalism_D5_PhiSet___redArg(v_inst_128_);
return v___x_129_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0(lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = ((lean_object*)(lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___closed__0));
v___x_135_ = l_instDecidableEqProd___redArg(v___x_134_, v___x_134_, v_a_132_, v_b_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0___boxed(lean_object* v_a_136_, lean_object* v_b_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__0(v_a_136_, v_b_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__1(lean_object* v___f_140_, lean_object* v_inst_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = l_instDecidableEqProd___redArg(v___f_140_, v_inst_141_, v_a_142_, v_b_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__1___boxed(lean_object* v___f_145_, lean_object* v_inst_146_, lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__1(v___f_145_, v_inst_146_, v_a_147_, v_b_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__2(lean_object* v_toAddSemigroup_151_, lean_object* v_u0_152_, lean_object* v_t_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_apply_2(v_toAddSemigroup_151_, v_t_153_, v_u0_152_);
v___x_155_ = lp_tree_Formalism_D5_thickPl___redArg(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_T2_159_, lean_object* v_u0_160_, lean_object* v_00_u03c1_161_){
_start:
{
lean_object* v_toAddMonoid_162_; lean_object* v_toAddSemigroup_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_toAddMonoid_162_ = lean_ctor_get(v_inst_157_, 0);
lean_inc_ref(v_toAddMonoid_162_);
lean_dec_ref(v_inst_157_);
v_toAddSemigroup_163_ = lean_ctor_get(v_toAddMonoid_162_, 0);
lean_inc(v_toAddSemigroup_163_);
lean_dec_ref(v_toAddMonoid_162_);
v___f_164_ = ((lean_object*)(lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___closed__0));
v___f_165_ = lean_alloc_closure((void*)(lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_165_, 0, v___f_164_);
lean_closure_set(v___f_165_, 1, v_inst_158_);
v___f_166_ = lean_alloc_closure((void*)(lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___lam__2), 3, 2);
lean_closure_set(v___f_166_, 0, v_toAddSemigroup_163_);
lean_closure_set(v___f_166_, 1, v_u0_160_);
lean_inc_ref(v___f_165_);
v___x_167_ = lp_mathlib_Finset_image___redArg(v___f_165_, v___f_166_, v_T2_159_);
v___x_168_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___f_165_, v_00_u03c1_161_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg___boxed(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_T2_171_, lean_object* v_u0_172_, lean_object* v_00_u03c1_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(v_inst_169_, v_inst_170_, v_T2_171_, v_u0_172_, v_00_u03c1_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1(lean_object* v_H_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_T2_179_, lean_object* v_u0_180_, lean_object* v_00_u03c1_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(v_inst_177_, v_inst_178_, v_T2_179_, v_u0_180_, v_00_u03c1_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___boxed(lean_object* v_H_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_T2_186_, lean_object* v_u0_187_, lean_object* v_00_u03c1_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1(v_H_183_, v_inst_184_, v_inst_185_, v_T2_186_, v_u0_187_, v_00_u03c1_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___redArg(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_T2_193_, lean_object* v_u0_194_, lean_object* v_00_u03c1_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(v_inst_191_, v_inst_192_, v_T2_193_, v_u0_194_, v_00_u03c1_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___redArg___boxed(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_T2_199_, lean_object* v_u0_200_, lean_object* v_00_u03c1_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___redArg(v_inst_197_, v_inst_198_, v_T2_199_, v_u0_200_, v_00_u03c1_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt(lean_object* v_H_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_T2_207_, lean_object* v_u0_208_, lean_object* v_00_u03c1_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(v_inst_205_, v_inst_206_, v_T2_207_, v_u0_208_, v_00_u03c1_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___boxed(lean_object* v_H_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_T2_214_, lean_object* v_u0_215_, lean_object* v_00_u03c1_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt(v_H_211_, v_inst_212_, v_inst_213_, v_T2_214_, v_u0_215_, v_00_u03c1_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThickAverageLoss_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_CorankShare_StatementFR(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Fourier_FiniteAbelian_PontryaginDuality(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThickAverageLoss_PartnersToFactorsAt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThickAverageLoss_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CorankShare_StatementFR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Fourier_FiniteAbelian_PontryaginDuality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
