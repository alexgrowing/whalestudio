// Lean compiler output
// Module: Formalism.LogVandermondeBounds.GaussOperatorProductFormula
// Imports: public import Init public meta import Init public import Formalism.LogVandermondeBounds.FinrankFiberSumZero
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
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_pair___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_unitsEquivProdSubtype(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_pmap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__0 = (const lean_object*)&lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__0_value;
static const lean_closure_object lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__0_value)} };
static const lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__1 = (const lean_object*)&lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__0(lean_object* v_val_1_, lean_object* v_property_2_){
_start:
{
lean_inc_ref(v_val_1_);
return v_val_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__0___boxed(lean_object* v_val_3_, lean_object* v_property_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__0(v_val_3_, v_property_4_);
lean_dec_ref(v_val_3_);
return v_res_5_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1(lean_object* v_toMul_6_, lean_object* v_inst_7_, lean_object* v_toOne_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v_fst_10_ = lean_ctor_get(v_a_9_, 0);
lean_inc_n(v_fst_10_, 2);
v_snd_11_ = lean_ctor_get(v_a_9_, 1);
lean_inc_n(v_snd_11_, 2);
lean_dec_ref(v_a_9_);
lean_inc(v_toMul_6_);
v___x_12_ = lean_apply_2(v_toMul_6_, v_fst_10_, v_snd_11_);
lean_inc_ref(v_inst_7_);
lean_inc(v_toOne_8_);
v___x_13_ = lean_apply_2(v_inst_7_, v___x_12_, v_toOne_8_);
v___x_14_ = lean_unbox(v___x_13_);
if (v___x_14_ == 0)
{
uint8_t v___x_15_; 
lean_dec(v_snd_11_);
lean_dec(v_fst_10_);
lean_dec(v_toOne_8_);
lean_dec_ref(v_inst_7_);
lean_dec(v_toMul_6_);
v___x_15_ = lean_unbox(v___x_13_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_16_ = lean_apply_2(v_toMul_6_, v_snd_11_, v_fst_10_);
v___x_17_ = lean_apply_2(v_inst_7_, v___x_16_, v_toOne_8_);
v___x_18_ = lean_unbox(v___x_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1___boxed(lean_object* v_toMul_19_, lean_object* v_inst_20_, lean_object* v_toOne_21_, lean_object* v_a_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1(v_toMul_19_, v_inst_20_, v_toOne_21_, v_a_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__2(lean_object* v___x_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_toFun_27_; lean_object* v___x_28_; 
v_toFun_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_toFun_27_);
lean_dec_ref(v___x_25_);
v___x_28_ = lean_apply_1(v_toFun_27_, v___y_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__3(lean_object* v_f_29_, lean_object* v_toMul_30_, lean_object* v_val_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_apply_1(v_f_29_, v___y_32_);
v___x_34_ = lean_apply_2(v_toMul_30_, v_val_31_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4(lean_object* v_00_u03c8_38_, lean_object* v_f_39_, lean_object* v_toMul_40_, lean_object* v_00_u03c6_41_, lean_object* v_c_42_){
_start:
{
lean_object* v_val_43_; lean_object* v___x_44_; lean_object* v_re_45_; lean_object* v_im_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v_val_43_ = lean_ctor_get(v_c_42_, 0);
lean_inc_n(v_val_43_, 2);
lean_dec_ref(v_c_42_);
v___x_44_ = lean_apply_1(v_00_u03c8_38_, v_val_43_);
v_re_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_re_45_);
v_im_46_ = lean_ctor_get(v___x_44_, 1);
lean_inc(v_im_46_);
lean_dec_ref(v___x_44_);
v___f_47_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__3), 4, 3);
lean_closure_set(v___f_47_, 0, v_f_39_);
lean_closure_set(v___f_47_, 1, v_toMul_40_);
lean_closure_set(v___f_47_, 2, v_val_43_);
v___x_48_ = lean_apply_1(v_00_u03c6_41_, v___f_47_);
v___f_49_ = ((lean_object*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__1));
v___x_50_ = lp_mathlib_Complex_mulAux___redArg(v___f_49_, v_re_45_, v_im_46_, v___x_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_00_u03c8_55_, lean_object* v_00_u03c6_56_, lean_object* v_f_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_toSemiring_61_; lean_object* v_toMonoid_62_; lean_object* v___x_63_; lean_object* v_toOne_64_; lean_object* v_toMul_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_toMul_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v___x_58_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_59_ = lp_mathlib_Field_toSemifield___redArg(v_inst_52_);
v___x_60_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_59_);
v_toSemiring_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_toSemiring_61_);
lean_dec_ref(v___x_60_);
v_toMonoid_62_ = lean_ctor_get(v_toSemiring_61_, 1);
lean_inc_ref(v_toMonoid_62_);
v___x_63_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_62_);
v_toOne_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_toOne_64_);
v_toMul_65_ = lean_ctor_get(v___x_63_, 1);
lean_inc(v_toMul_65_);
lean_dec_ref(v___x_63_);
lean_inc(v_inst_53_);
v___x_66_ = lp_mathlib_Multiset_product___redArg(v_inst_53_, v_inst_53_);
v___x_67_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_61_);
v_toMul_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_toMul_68_);
lean_dec_ref(v___x_67_);
v___f_69_ = ((lean_object*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___closed__0));
v___f_70_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_70_, 0, v_toMul_65_);
lean_closure_set(v___f_70_, 1, v_inst_54_);
lean_closure_set(v___f_70_, 2, v_toOne_64_);
v___x_71_ = lp_mathlib_unitsEquivProdSubtype(lean_box(0), v_toMonoid_62_);
lean_dec_ref(v_toMonoid_62_);
v___x_72_ = lp_mathlib_Equiv_symm___redArg(v___x_71_);
v___f_73_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__2), 2, 1);
lean_closure_set(v___f_73_, 0, v___x_72_);
v___x_74_ = lp_mathlib_Multiset_filter___redArg(v___f_70_, v___x_66_);
v___x_75_ = lp_mathlib_Multiset_pmap___redArg(v___f_69_, v___x_74_);
v___x_76_ = lp_mathlib_Finset_map___redArg(v___f_73_, v___x_75_);
v___f_77_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4), 5, 4);
lean_closure_set(v___f_77_, 0, v_00_u03c8_55_);
lean_closure_set(v___f_77_, 1, v_f_57_);
lean_closure_set(v___f_77_, 2, v_toMul_68_);
lean_closure_set(v___f_77_, 3, v_00_u03c6_56_);
v___x_78_ = lp_mathlib_Finset_sum___redArg(v___x_58_, v___x_76_, v___f_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___boxed(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_00_u03c8_82_, lean_object* v_00_u03c6_83_, lean_object* v_f_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg(v_inst_79_, v_inst_80_, v_inst_81_, v_00_u03c8_82_, v_00_u03c6_83_, v_f_84_);
lean_dec_ref(v_inst_79_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs(lean_object* v_k_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_r_90_, lean_object* v_00_u03c8_91_, lean_object* v_00_u03c6_92_, lean_object* v_f_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg(v_inst_87_, v_inst_88_, v_inst_89_, v_00_u03c8_91_, v_00_u03c6_92_, v_f_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___boxed(lean_object* v_k_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_r_99_, lean_object* v_00_u03c8_100_, lean_object* v_00_u03c6_101_, lean_object* v_f_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs(v_k_95_, v_inst_96_, v_inst_97_, v_inst_98_, v_r_99_, v_00_u03c8_100_, v_00_u03c6_101_, v_f_102_);
lean_dec(v_r_99_);
lean_dec_ref(v_inst_96_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___lam__3(lean_object* v_f_104_, lean_object* v_toMul_105_, lean_object* v_inv_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_apply_1(v_f_104_, v___y_107_);
v___x_109_ = lean_apply_2(v_toMul_105_, v_inv_106_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___lam__0(lean_object* v_00_u03c8_110_, lean_object* v_f_111_, lean_object* v_toMul_112_, lean_object* v_00_u03c6_113_, lean_object* v_c_114_){
_start:
{
lean_object* v_val_115_; lean_object* v_inv_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_re_119_; lean_object* v_im_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___x_124_; 
v_val_115_ = lean_ctor_get(v_c_114_, 0);
lean_inc(v_val_115_);
v_inv_116_ = lean_ctor_get(v_c_114_, 1);
lean_inc(v_inv_116_);
lean_dec_ref(v_c_114_);
v___x_117_ = lean_apply_1(v_00_u03c8_110_, v_val_115_);
v___x_118_ = lp_mathlib_Complex_instStarRing___lam__0(v___x_117_);
v_re_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_re_119_);
v_im_120_ = lean_ctor_get(v___x_118_, 1);
lean_inc(v_im_120_);
lean_dec_ref(v___x_118_);
v___f_121_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___lam__3), 4, 3);
lean_closure_set(v___f_121_, 0, v_f_111_);
lean_closure_set(v___f_121_, 1, v_toMul_112_);
lean_closure_set(v___f_121_, 2, v_inv_116_);
v___x_122_ = lean_apply_1(v_00_u03c6_113_, v___f_121_);
v___f_123_ = ((lean_object*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__1));
v___x_124_ = lp_mathlib_Complex_mulAux___redArg(v___f_123_, v_re_119_, v_im_120_, v___x_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg(lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_00_u03c8_128_, lean_object* v_00_u03c6_129_, lean_object* v_f_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_toSemiring_134_; lean_object* v_toMonoid_135_; lean_object* v___x_136_; lean_object* v_toOne_137_; lean_object* v_toMul_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_toMul_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_151_; 
v___x_131_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_132_ = lp_mathlib_Field_toSemifield___redArg(v_inst_125_);
v___x_133_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_132_);
v_toSemiring_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_toSemiring_134_);
lean_dec_ref(v___x_133_);
v_toMonoid_135_ = lean_ctor_get(v_toSemiring_134_, 1);
lean_inc_ref(v_toMonoid_135_);
v___x_136_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_135_);
v_toOne_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_toOne_137_);
v_toMul_138_ = lean_ctor_get(v___x_136_, 1);
lean_inc(v_toMul_138_);
lean_dec_ref(v___x_136_);
lean_inc(v_inst_126_);
v___x_139_ = lp_mathlib_Multiset_product___redArg(v_inst_126_, v_inst_126_);
v___x_140_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_134_);
v_toMul_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_toMul_141_);
lean_dec_ref(v___x_140_);
v___f_142_ = ((lean_object*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___closed__0));
v___f_143_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_143_, 0, v_toMul_138_);
lean_closure_set(v___f_143_, 1, v_inst_127_);
lean_closure_set(v___f_143_, 2, v_toOne_137_);
v___x_144_ = lp_mathlib_unitsEquivProdSubtype(lean_box(0), v_toMonoid_135_);
lean_dec_ref(v_toMonoid_135_);
v___x_145_ = lp_mathlib_Equiv_symm___redArg(v___x_144_);
v___f_146_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__2), 2, 1);
lean_closure_set(v___f_146_, 0, v___x_145_);
v___x_147_ = lp_mathlib_Multiset_filter___redArg(v___f_143_, v___x_139_);
v___x_148_ = lp_mathlib_Multiset_pmap___redArg(v___f_142_, v___x_147_);
v___x_149_ = lp_mathlib_Finset_map___redArg(v___f_146_, v___x_148_);
v___f_150_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___lam__0), 5, 4);
lean_closure_set(v___f_150_, 0, v_00_u03c8_128_);
lean_closure_set(v___f_150_, 1, v_f_130_);
lean_closure_set(v___f_150_, 2, v_toMul_141_);
lean_closure_set(v___f_150_, 3, v_00_u03c6_129_);
v___x_151_ = lp_mathlib_Finset_sum___redArg(v___x_131_, v___x_149_, v___f_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg___boxed(lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_00_u03c8_155_, lean_object* v_00_u03c6_156_, lean_object* v_f_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg(v_inst_152_, v_inst_153_, v_inst_154_, v_00_u03c8_155_, v_00_u03c6_156_, v_f_157_);
lean_dec_ref(v_inst_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar(lean_object* v_k_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_r_163_, lean_object* v_00_u03c8_164_, lean_object* v_00_u03c6_165_, lean_object* v_f_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___redArg(v_inst_160_, v_inst_161_, v_inst_162_, v_00_u03c8_164_, v_00_u03c6_165_, v_f_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar___boxed(lean_object* v_k_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_r_172_, lean_object* v_00_u03c8_173_, lean_object* v_00_u03c6_174_, lean_object* v_f_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGsStar(v_k_168_, v_inst_169_, v_inst_170_, v_inst_171_, v_r_172_, v_00_u03c8_173_, v_00_u03c6_174_, v_f_175_);
lean_dec(v_r_172_);
lean_dec_ref(v_inst_169_);
return v_res_176_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__0(lean_object* v_inst_177_, lean_object* v_a_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_apply_2(v_inst_177_, v___y_179_, v___y_180_);
v___x_182_ = lean_unbox(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__0___boxed(lean_object* v_inst_183_, lean_object* v_a_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__0(v_inst_183_, v_a_184_, v___y_185_, v___y_186_);
lean_dec(v_a_184_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__1(lean_object* v_inst_189_, lean_object* v_x_190_){
_start:
{
lean_inc(v_inst_189_);
return v_inst_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__1___boxed(lean_object* v_inst_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__1(v_inst_191_, v_x_192_);
lean_dec(v_x_192_);
lean_dec(v_inst_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__2(lean_object* v_inst_194_, lean_object* v_r_195_, lean_object* v_x_196_, lean_object* v_00_u03c8_197_, lean_object* v_00_u03c6_198_, lean_object* v_f_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_re_202_; lean_object* v_im_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; 
lean_inc(v_f_199_);
v___x_200_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_pair___redArg(v_inst_194_, v_r_195_, v_f_199_, v_x_196_);
v___x_201_ = lean_apply_1(v_00_u03c8_197_, v___x_200_);
v_re_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_re_202_);
v_im_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_im_203_);
lean_dec_ref(v___x_201_);
v___x_204_ = lean_apply_1(v_00_u03c6_198_, v_f_199_);
v___f_205_ = ((lean_object*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opGs___redArg___lam__4___closed__1));
v___x_206_ = lp_mathlib_Complex_mulAux___redArg(v___f_205_, v_re_202_, v_im_203_, v___x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__2___boxed(lean_object* v_inst_207_, lean_object* v_r_208_, lean_object* v_x_209_, lean_object* v_00_u03c8_210_, lean_object* v_00_u03c6_211_, lean_object* v_f_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__2(v_inst_207_, v_r_208_, v_x_209_, v_00_u03c8_210_, v_00_u03c6_211_, v_f_212_);
lean_dec_ref(v_inst_207_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__3(lean_object* v_toZero_214_, lean_object* v_x_215_){
_start:
{
lean_inc(v_toZero_214_);
return v_toZero_214_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__3___boxed(lean_object* v_toZero_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__3(v_toZero_216_, v_x_217_);
lean_dec(v_x_217_);
lean_dec(v_toZero_216_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__4(lean_object* v___f_219_, lean_object* v___x_220_, lean_object* v___f_221_, lean_object* v_a_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_219_, v___x_220_, v_a_222_, v___f_221_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 1;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 0;
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__4___boxed(lean_object* v___f_226_, lean_object* v___x_227_, lean_object* v___f_228_, lean_object* v_a_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__4(v___f_226_, v___x_227_, v___f_228_, v_a_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_r_235_, lean_object* v_00_u03c8_236_, lean_object* v_00_u03c6_237_, lean_object* v_x_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_toSemiring_242_; lean_object* v___x_243_; lean_object* v_toZero_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_239_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_240_ = lp_mathlib_Field_toSemifield___redArg(v_inst_232_);
v___x_241_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_240_);
v_toSemiring_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_toSemiring_242_);
lean_dec_ref(v___x_241_);
v___x_243_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_242_);
v_toZero_244_ = lean_ctor_get(v___x_243_, 1);
lean_inc(v_toZero_244_);
lean_dec_ref(v___x_243_);
v___f_245_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_245_, 0, v_inst_234_);
v___f_246_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_246_, 0, v_inst_233_);
lean_inc_n(v_r_235_, 2);
v___f_247_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_247_, 0, v_inst_232_);
lean_closure_set(v___f_247_, 1, v_r_235_);
lean_closure_set(v___f_247_, 2, v_x_238_);
lean_closure_set(v___f_247_, 3, v_00_u03c8_236_);
lean_closure_set(v___f_247_, 4, v_00_u03c6_237_);
v___x_248_ = l_List_finRange(v_r_235_);
v___f_249_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_249_, 0, v_toZero_244_);
lean_inc(v___x_248_);
v___f_250_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_250_, 0, v___f_245_);
lean_closure_set(v___f_250_, 1, v___x_248_);
lean_closure_set(v___f_250_, 2, v___f_249_);
v___x_251_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_251_, 0, v_r_235_);
v___x_252_ = lp_mathlib_Fintype_piFinset___redArg(v___x_251_, v___x_248_, v___f_246_);
v___x_253_ = lp_mathlib_Multiset_filter___redArg(v___f_250_, v___x_252_);
v___x_254_ = lp_mathlib_Finset_sum___redArg(v___x_239_, v___x_253_, v___f_247_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF(lean_object* v_k_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_r_259_, lean_object* v_00_u03c8_260_, lean_object* v_00_u03c6_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_opFF___redArg(v_inst_256_, v_inst_257_, v_inst_258_, v_r_259_, v_00_u03c8_260_, v_00_u03c6_261_, v_x_262_);
return v___x_263_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogVandermondeBounds_FinrankFiberSumZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LogVandermondeBounds_GaussOperatorProductFormula(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogVandermondeBounds_FinrankFiberSumZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
