// Lean compiler output
// Module: Formalism.GL3MeanSquares.AffineFibreCountComparison
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
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
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_pair___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__0 = (const lean_object*)&lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__0_value;
static const lean_closure_object lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__0_value)} };
static const lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__1 = (const lean_object*)&lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_apply_2(v_inst_1_, v___y_3_, v___y_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__0(v_inst_7_, v_a_8_, v___y_9_, v___y_10_);
lean_dec(v_a_8_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__1(lean_object* v_inst_13_, lean_object* v_x_14_){
_start:
{
lean_inc(v_inst_13_);
return v_inst_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__1___boxed(lean_object* v_inst_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__1(v_inst_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec(v_inst_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__2(lean_object* v_toZero_18_, lean_object* v_x_19_){
_start:
{
lean_inc(v_toZero_18_);
return v_toZero_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__2___boxed(lean_object* v_toZero_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__2(v_toZero_20_, v_x_21_);
lean_dec(v_x_21_);
lean_dec(v_toZero_20_);
return v_res_22_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__3(lean_object* v___f_23_, lean_object* v___x_24_, lean_object* v___f_25_, lean_object* v_a_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_23_, v___x_24_, v_a_26_, v___f_25_);
if (v___x_27_ == 0)
{
uint8_t v___x_28_; 
v___x_28_ = 1;
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = 0;
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__3___boxed(lean_object* v___f_30_, lean_object* v___x_31_, lean_object* v___f_32_, lean_object* v_a_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__3(v___f_30_, v___x_31_, v___f_32_, v_a_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4(lean_object* v_inst_39_, lean_object* v_r_40_, lean_object* v_f_41_, lean_object* v_toNeg_42_, lean_object* v_00_u03c8_43_, lean_object* v_00_u03c6_x27_44_, lean_object* v_x_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_re_49_; lean_object* v_im_50_; lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
lean_inc(v_x_45_);
v___x_46_ = lp_tree_Formalism_LogVandermondeBounds_product__first__zeroth__parts_pair___redArg(v_inst_39_, v_r_40_, v_f_41_, v_x_45_);
v___x_47_ = lean_apply_1(v_toNeg_42_, v___x_46_);
v___x_48_ = lean_apply_1(v_00_u03c8_43_, v___x_47_);
v_re_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_re_49_);
v_im_50_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_im_50_);
lean_dec_ref(v___x_48_);
v___x_51_ = lean_apply_1(v_00_u03c6_x27_44_, v_x_45_);
v___f_52_ = ((lean_object*)(lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___closed__1));
v___x_53_ = lp_mathlib_Complex_mulAux___redArg(v___f_52_, v_re_49_, v_im_50_, v___x_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___boxed(lean_object* v_inst_54_, lean_object* v_r_55_, lean_object* v_f_56_, lean_object* v_toNeg_57_, lean_object* v_00_u03c8_58_, lean_object* v_00_u03c6_x27_59_, lean_object* v_x_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4(v_inst_54_, v_r_55_, v_f_56_, v_toNeg_57_, v_00_u03c8_58_, v_00_u03c6_x27_59_, v_x_60_);
lean_dec_ref(v_inst_54_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_r_65_, lean_object* v_00_u03c8_66_, lean_object* v_00_u03c6_x27_67_, lean_object* v_f_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_toSemiring_72_; lean_object* v___x_73_; lean_object* v_toZero_74_; lean_object* v___x_75_; lean_object* v_toRing_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_toNeg_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_69_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_70_ = lp_mathlib_Field_toSemifield___redArg(v_inst_62_);
v___x_71_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_70_);
v_toSemiring_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_toSemiring_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_72_);
v_toZero_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_toZero_74_);
lean_dec_ref(v___x_73_);
lean_inc_ref(v_inst_62_);
v___x_75_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_62_);
v_toRing_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_toRing_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_76_);
lean_dec_ref(v_toRing_76_);
v___x_78_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_77_);
lean_dec_ref(v___x_77_);
v_toNeg_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_toNeg_79_);
lean_dec_ref(v___x_78_);
v___f_80_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_80_, 0, v_inst_64_);
v___f_81_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_81_, 0, v_inst_63_);
lean_inc_n(v_r_65_, 2);
v___x_82_ = l_List_finRange(v_r_65_);
v___f_83_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_83_, 0, v_toZero_74_);
lean_inc(v___x_82_);
v___f_84_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_84_, 0, v___f_80_);
lean_closure_set(v___f_84_, 1, v___x_82_);
lean_closure_set(v___f_84_, 2, v___f_83_);
v___f_85_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_85_, 0, v_inst_62_);
lean_closure_set(v___f_85_, 1, v_r_65_);
lean_closure_set(v___f_85_, 2, v_f_68_);
lean_closure_set(v___f_85_, 3, v_toNeg_79_);
lean_closure_set(v___f_85_, 4, v_00_u03c8_66_);
lean_closure_set(v___f_85_, 5, v_00_u03c6_x27_67_);
v___x_86_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_86_, 0, v_r_65_);
v___x_87_ = lp_mathlib_Fintype_piFinset___redArg(v___x_86_, v___x_82_, v___f_81_);
v___x_88_ = lp_mathlib_Multiset_filter___redArg(v___f_84_, v___x_87_);
v___x_89_ = lp_mathlib_Finset_sum___redArg(v___x_69_, v___x_88_, v___f_85_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar(lean_object* v_F_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_r_94_, lean_object* v_00_u03c8_95_, lean_object* v_00_u03c6_x27_96_, lean_object* v_f_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_tree_Formalism_HermitianLattices_RamifiedLatticeOperators_opFFstar___redArg(v_inst_91_, v_inst_92_, v_inst_93_, v_r_94_, v_00_u03c8_95_, v_00_u03c6_x27_96_, v_f_97_);
return v___x_98_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GL3MeanSquares_AffineFibreCountComparison(uint8_t builtin) {
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
res = initialize_tree_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
