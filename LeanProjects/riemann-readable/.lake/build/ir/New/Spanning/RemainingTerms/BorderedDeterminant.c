// Lean compiler output
// Module: New.Spanning.RemainingTerms.BorderedDeterminant
// Imports: public import Init public meta import Init public import New.Spanning.Unfolding.Link
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Fin_castSucc___boxed(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
lean_object* lp_GRH_New_Filling_frameProducts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_frameImage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toRows_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toRows_u2081___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
static const lean_closure_object lp_GRH_New_Filling_isotropicRows___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Filling_isotropicRows___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Filling_isotropicRows___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicRows___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicRows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Filling_paddedLeading___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Filling_paddedLeading___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_frameMiddle___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_frameMiddle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Filling_subframeIndices___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeIndices___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Filling_subframeMinor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_subframeMinor___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Filling_subframeMinor___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Filling_subframeMinor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_subframeMinor___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_subframeMinor___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Filling_subframeMinor___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicRows___redArg(lean_object* v_00_U0001d530_2_, lean_object* v_Z_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_00_u03f1_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_00_u03f1_6_ = lean_ctor_get(v_00_U0001d530_2_, 0);
lean_inc(v_00_u03f1_6_);
lean_dec_ref(v_00_U0001d530_2_);
v___x_7_ = lean_alloc_closure((void*)(l_Fin_castSucc___boxed), 2, 1);
lean_closure_set(v___x_7_, 0, v_00_u03f1_6_);
v___x_8_ = ((lean_object*)(lp_GRH_New_Filling_isotropicRows___redArg___closed__0));
v___x_9_ = lp_mathlib_Matrix_submatrix___redArg(v_Z_3_, v___x_7_, v___x_8_, v_a_4_, v_a_5_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicRows(lean_object* v_00_U0001d530_10_, lean_object* v_R_11_, lean_object* v_Z_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_00_u03f1_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_00_u03f1_15_ = lean_ctor_get(v_00_U0001d530_10_, 0);
lean_inc(v_00_u03f1_15_);
lean_dec_ref(v_00_U0001d530_10_);
v___x_16_ = lean_alloc_closure((void*)(l_Fin_castSucc___boxed), 2, 1);
lean_closure_set(v___x_16_, 0, v_00_u03f1_15_);
v___x_17_ = ((lean_object*)(lp_GRH_New_Filling_isotropicRows___redArg___closed__0));
v___x_18_ = lp_mathlib_Matrix_submatrix___redArg(v_Z_12_, v___x_16_, v___x_17_, v_a_13_, v_a_14_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___redArg___lam__0(lean_object* v_j_19_, lean_object* v_toZero_20_, lean_object* v_toOne_21_, lean_object* v_Z_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = lean_nat_dec_lt(v_a_23_, v_j_19_);
if (v___x_25_ == 0)
{
uint8_t v___x_26_; 
lean_dec(v_Z_22_);
v___x_26_ = lean_nat_dec_eq(v_a_23_, v_b_24_);
lean_dec(v_b_24_);
lean_dec(v_a_23_);
if (v___x_26_ == 0)
{
lean_inc(v_toZero_20_);
return v_toZero_20_;
}
else
{
lean_inc(v_toOne_21_);
return v_toOne_21_;
}
}
else
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_2(v_Z_22_, v_a_23_, v_b_24_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___redArg___lam__0___boxed(lean_object* v_j_28_, lean_object* v_toZero_29_, lean_object* v_toOne_30_, lean_object* v_Z_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_Filling_paddedLeading___redArg___lam__0(v_j_28_, v_toZero_29_, v_toOne_30_, v_Z_31_, v_a_32_, v_b_33_);
lean_dec(v_toOne_30_);
lean_dec(v_toZero_29_);
lean_dec(v_j_28_);
return v_res_34_;
}
}
static lean_object* _init_lp_GRH_New_Filling_paddedLeading___redArg___closed__0(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_mathlib_Equiv_refl___redArg();
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___redArg(lean_object* v_j_36_, lean_object* v_Z_37_, lean_object* v_inst_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_toSemiring_41_; lean_object* v___x_42_; lean_object* v_toZero_43_; lean_object* v___x_44_; lean_object* v_toAddMonoidWithOne_45_; lean_object* v_toOne_46_; lean_object* v___x_47_; lean_object* v_toFun_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v_toSemiring_41_ = lean_ctor_get(v_inst_38_, 0);
lean_inc_ref(v_toSemiring_41_);
v___x_42_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_41_);
v_toZero_43_ = lean_ctor_get(v___x_42_, 1);
lean_inc(v_toZero_43_);
lean_dec_ref(v___x_42_);
v___x_44_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_38_);
v_toAddMonoidWithOne_45_ = lean_ctor_get(v___x_44_, 1);
lean_inc_ref(v_toAddMonoidWithOne_45_);
lean_dec_ref(v___x_44_);
v_toOne_46_ = lean_ctor_get(v_toAddMonoidWithOne_45_, 2);
lean_inc(v_toOne_46_);
lean_dec_ref(v_toAddMonoidWithOne_45_);
v___x_47_ = lean_obj_once(&lp_GRH_New_Filling_paddedLeading___redArg___closed__0, &lp_GRH_New_Filling_paddedLeading___redArg___closed__0_once, _init_lp_GRH_New_Filling_paddedLeading___redArg___closed__0);
v_toFun_48_ = lean_ctor_get(v___x_47_, 0);
v___f_49_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_paddedLeading___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_49_, 0, v_j_36_);
lean_closure_set(v___f_49_, 1, v_toZero_43_);
lean_closure_set(v___f_49_, 2, v_toOne_46_);
lean_closure_set(v___f_49_, 3, v_Z_37_);
lean_inc(v_toFun_48_);
v___x_50_ = lean_apply_3(v_toFun_48_, v___f_49_, v_a_39_, v_a_40_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading(lean_object* v_00_U0001d530_51_, lean_object* v_R_52_, lean_object* v_j_53_, lean_object* v_Z_54_, lean_object* v_inst_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_GRH_New_Filling_paddedLeading___redArg(v_j_53_, v_Z_54_, v_inst_55_, v_a_56_, v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_paddedLeading___boxed(lean_object* v_00_U0001d530_59_, lean_object* v_R_60_, lean_object* v_j_61_, lean_object* v_Z_62_, lean_object* v_inst_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_GRH_New_Filling_paddedLeading(v_00_U0001d530_59_, v_R_60_, v_j_61_, v_Z_62_, v_inst_63_, v_a_64_, v_a_65_);
lean_dec_ref(v_00_U0001d530_59_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_frameMiddle___redArg(lean_object* v_00_U0001d530_67_, lean_object* v_00_u03b3_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_alloc_closure((void*)(lp_GRH_New_frameImage), 5, 3);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, v_00_U0001d530_67_);
lean_closure_set(v___x_71_, 2, v_00_u03b3_68_);
v___x_72_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toRows_u2082), 7, 5);
lean_closure_set(v___x_72_, 0, lean_box(0));
lean_closure_set(v___x_72_, 1, lean_box(0));
lean_closure_set(v___x_72_, 2, lean_box(0));
lean_closure_set(v___x_72_, 3, lean_box(0));
lean_closure_set(v___x_72_, 4, v___x_71_);
v___x_73_ = lp_mathlib_Matrix_toRows_u2081___redArg(v___x_72_, v_a_69_, v_a_70_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_frameMiddle(lean_object* v_00_U0001d530_74_, lean_object* v_R_75_, lean_object* v_00_u03b3_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_alloc_closure((void*)(lp_GRH_New_frameImage), 5, 3);
lean_closure_set(v___x_79_, 0, lean_box(0));
lean_closure_set(v___x_79_, 1, v_00_U0001d530_74_);
lean_closure_set(v___x_79_, 2, v_00_u03b3_76_);
v___x_80_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toRows_u2082), 7, 5);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, lean_box(0));
lean_closure_set(v___x_80_, 2, lean_box(0));
lean_closure_set(v___x_80_, 3, lean_box(0));
lean_closure_set(v___x_80_, 4, v___x_79_);
v___x_81_ = lp_mathlib_Matrix_toRows_u2081___redArg(v___x_80_, v_a_77_, v_a_78_);
return v___x_81_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Filling_subframeIndices___lam__0(lean_object* v_j_82_, lean_object* v_00_u03f1_83_, lean_object* v_a_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = lean_nat_dec_lt(v_a_84_, v_j_82_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_eq(v_a_84_, v_00_u03f1_83_);
return v___x_86_;
}
else
{
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeIndices___lam__0___boxed(lean_object* v_j_87_, lean_object* v_00_u03f1_88_, lean_object* v_a_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = lp_GRH_New_Filling_subframeIndices___lam__0(v_j_87_, v_00_u03f1_88_, v_a_89_);
lean_dec(v_a_89_);
lean_dec(v_00_u03f1_88_);
lean_dec(v_j_87_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeIndices(lean_object* v_00_U0001d530_92_, lean_object* v_j_93_){
_start:
{
lean_object* v_00_u03f1_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_00_u03f1_94_ = lean_ctor_get(v_00_U0001d530_92_, 0);
lean_inc_n(v_00_u03f1_94_, 2);
lean_dec_ref(v_00_U0001d530_92_);
v___f_95_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_subframeIndices___lam__0___boxed), 3, 2);
lean_closure_set(v___f_95_, 0, v_j_93_);
lean_closure_set(v___f_95_, 1, v_00_u03f1_94_);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_add(v_00_u03f1_94_, v___x_96_);
lean_dec(v_00_u03f1_94_);
v___x_98_ = l_List_finRange(v___x_97_);
v___x_99_ = lp_mathlib_Multiset_filter___redArg(v___f_95_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor___redArg___lam__1(lean_object* v_self_100_){
_start:
{
lean_inc(v_self_100_);
return v_self_100_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor___redArg___lam__1___boxed(lean_object* v_self_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_GRH_New_Filling_subframeMinor___redArg___lam__1(v_self_101_);
lean_dec(v_self_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor___redArg(lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_00_U0001d530_107_, lean_object* v_S_108_, lean_object* v_j_109_, lean_object* v_00_u03b3_110_){
_start:
{
lean_object* v_toCommRing_111_; lean_object* v_00_u03f1_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_58__overap_123_; lean_object* v___x_124_; 
v_toCommRing_111_ = lean_ctor_get(v_inst_105_, 0);
lean_inc_ref(v_toCommRing_111_);
v_00_u03f1_112_ = lean_ctor_get(v_00_U0001d530_107_, 0);
v___f_113_ = ((lean_object*)(lp_GRH_New_Filling_subframeMinor___redArg___closed__0));
lean_inc(v_00_u03f1_112_);
v___f_114_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_subframeIndices___lam__0___boxed), 3, 2);
lean_closure_set(v___f_114_, 0, v_j_109_);
lean_closure_set(v___f_114_, 1, v_00_u03f1_112_);
v___f_115_ = ((lean_object*)(lp_GRH_New_Filling_subframeMinor___redArg___closed__1));
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_00_u03f1_112_, v___x_116_);
v___x_118_ = l_List_finRange(v___x_117_);
v___x_119_ = lp_mathlib_Multiset_filter___redArg(v___f_114_, v___x_118_);
v___x_120_ = lp_mathlib_Multiset_attach___redArg(v___x_119_);
v___x_121_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_frameProducts), 8, 6);
lean_closure_set(v___x_121_, 0, lean_box(0));
lean_closure_set(v___x_121_, 1, v_inst_105_);
lean_closure_set(v___x_121_, 2, v_inst_106_);
lean_closure_set(v___x_121_, 3, v_00_U0001d530_107_);
lean_closure_set(v___x_121_, 4, v_S_108_);
lean_closure_set(v___x_121_, 5, v_00_u03b3_110_);
v___x_122_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_122_, 0, lean_box(0));
lean_closure_set(v___x_122_, 1, lean_box(0));
lean_closure_set(v___x_122_, 2, lean_box(0));
lean_closure_set(v___x_122_, 3, lean_box(0));
lean_closure_set(v___x_122_, 4, lean_box(0));
lean_closure_set(v___x_122_, 5, v___x_121_);
lean_closure_set(v___x_122_, 6, v___f_115_);
lean_closure_set(v___x_122_, 7, v___f_115_);
v___x_58__overap_123_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___f_113_, v___x_120_, v_toCommRing_111_);
v___x_124_ = lean_apply_1(v___x_58__overap_123_, v___x_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_subframeMinor(lean_object* v_E_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_00_U0001d530_128_, lean_object* v_S_129_, lean_object* v_j_130_, lean_object* v_00_u03b3_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_GRH_New_Filling_subframeMinor___redArg(v_inst_126_, v_inst_127_, v_00_U0001d530_128_, v_S_129_, v_j_130_, v_00_u03b3_131_);
return v___x_132_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_Link(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_BorderedDeterminant(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_Unfolding_Link(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
