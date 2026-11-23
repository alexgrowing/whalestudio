// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.Statement
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HarderNarasimhan.StatementPl public import Formalism.HermitianLattices.StatementLat
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
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toLinearMap_u209b_u2097_u2082_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_mulVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NumberField_RingOfIntegers_mapRingEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_conjPl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_conjPl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_DivisionValues_hform___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DivisionValues_hform___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_DivisionValues_hform___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_DivisionValues_gramR___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_matLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_matLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
lean_inc(v_inst_2_);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_inst_2_);
lean_ctor_set(v___x_3_, 1, v_inst_2_);
v___x_4_ = lp_mathlib_NumberField_RingOfIntegers_mapRingEquiv___redArg(v_inst_1_, v_inst_1_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO___redArg___boxed(lean_object* v_inst_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_tree_Formalism_DivisionValues_cO___redArg(v_inst_5_, v_inst_6_);
lean_dec_ref(v_inst_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO(lean_object* v_K_8_, lean_object* v_inst_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_tree_Formalism_DivisionValues_cO___redArg(v_inst_9_, v_inst_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cO___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_DivisionValues_cO(v_K_12_, v_inst_13_, v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_conjPl(lean_object* v_K_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_w_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_conjPl___boxed(lean_object* v_K_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_w_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_DivisionValues_conjPl(v_K_21_, v_inst_22_, v_inst_23_, v_w_24_);
lean_dec(v_inst_23_);
lean_dec_ref(v_inst_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform___redArg(lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_H_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v_toSemiring_33_; lean_object* v_toAddCommMonoid_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v_toLinearMap_40_; lean_object* v___x_41_; 
v___x_31_ = lp_mathlib_Field_toSemifield___redArg(v_inst_27_);
v___x_32_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_31_);
v_toSemiring_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc_ref_n(v_toSemiring_33_, 4);
lean_dec_ref(v___x_32_);
v_toAddCommMonoid_34_ = lean_ctor_get(v_toSemiring_33_, 0);
lean_inc_ref(v_toAddCommMonoid_34_);
v___x_35_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_33_);
lean_inc(v_n_29_);
v___x_36_ = l_List_finRange(v_n_29_);
v___f_37_ = ((lean_object*)(lp_tree_Formalism_DivisionValues_hform___redArg___closed__0));
v___x_38_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_38_, 0, v_n_29_);
lean_inc_ref(v___x_38_);
lean_inc(v___x_36_);
lean_inc(v___x_35_);
v___x_39_ = lp_mathlib_Matrix_toLinearMap_u209b_u2097_u2082_x27___redArg(v_toAddCommMonoid_34_, v_toSemiring_33_, v_toSemiring_33_, v_toSemiring_33_, v_toSemiring_33_, v___x_35_, v___x_35_, v_inst_28_, v___f_37_, v___x_36_, v___x_36_, v___x_38_, v___x_38_);
v_toLinearMap_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_toLinearMap_40_);
lean_dec_ref(v___x_39_);
v___x_41_ = lean_apply_1(v_toLinearMap_40_, v_H_30_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform___redArg___boxed(lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_n_44_, lean_object* v_H_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Formalism_DivisionValues_hform___redArg(v_inst_42_, v_inst_43_, v_n_44_, v_H_45_);
lean_dec_ref(v_inst_42_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform(lean_object* v_K_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_n_50_, lean_object* v_H_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_tree_Formalism_DivisionValues_hform___redArg(v_inst_48_, v_inst_49_, v_n_50_, v_H_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_hform___boxed(lean_object* v_K_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_n_56_, lean_object* v_H_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_DivisionValues_hform(v_K_53_, v_inst_54_, v_inst_55_, v_n_56_, v_H_57_);
lean_dec_ref(v_inst_54_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___lam__0(lean_object* v_e_59_, lean_object* v_a_60_, lean_object* v_inst_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_apply_2(v_e_59_, v_a_60_, v___y_62_);
v___x_64_ = lean_apply_1(v_inst_61_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___lam__1(lean_object* v_e_65_, lean_object* v_inst_66_, lean_object* v___x_67_, lean_object* v___x_68_, lean_object* v_00_u0393_69_, lean_object* v_toMul_70_, lean_object* v_toAddCommMonoid_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_inc(v_e_65_);
v___f_74_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_gramR___redArg___lam__0), 4, 3);
lean_closure_set(v___f_74_, 0, v_e_65_);
lean_closure_set(v___f_74_, 1, v_a_72_);
lean_closure_set(v___f_74_, 2, v_inst_66_);
v___x_75_ = lean_apply_1(v_e_65_, v_b_73_);
lean_inc(v___x_68_);
v___x_76_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_mulVec), 8, 7);
lean_closure_set(v___x_76_, 0, lean_box(0));
lean_closure_set(v___x_76_, 1, lean_box(0));
lean_closure_set(v___x_76_, 2, lean_box(0));
lean_closure_set(v___x_76_, 3, v___x_67_);
lean_closure_set(v___x_76_, 4, v___x_68_);
lean_closure_set(v___x_76_, 5, v_00_u0393_69_);
lean_closure_set(v___x_76_, 6, v___x_75_);
v___x_77_ = lp_mathlib_dotProduct___redArg(v___x_68_, v_toMul_70_, v_toAddCommMonoid_71_, v___f_74_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg___lam__1___boxed(lean_object* v_e_78_, lean_object* v_inst_79_, lean_object* v___x_80_, lean_object* v___x_81_, lean_object* v_00_u0393_82_, lean_object* v_toMul_83_, lean_object* v_toAddCommMonoid_84_, lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_DivisionValues_gramR___redArg___lam__1(v_e_78_, v_inst_79_, v___x_80_, v___x_81_, v_00_u0393_82_, v_toMul_83_, v_toAddCommMonoid_84_, v_a_85_, v_b_86_);
lean_dec_ref(v_toAddCommMonoid_84_);
return v_res_87_;
}
}
static lean_object* _init_lp_tree_Formalism_DivisionValues_gramR___redArg___closed__0(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR___redArg(lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_D_91_, lean_object* v_m_92_, lean_object* v_00_u0393_93_, lean_object* v_e_94_){
_start:
{
lean_object* v_toCommRing_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_toSemiring_98_; lean_object* v___x_99_; lean_object* v_toMul_100_; lean_object* v_toAddCommMonoid_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_toFun_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_95__overap_111_; lean_object* v___x_112_; 
v_toCommRing_95_ = lean_ctor_get(v_inst_89_, 0);
lean_inc_ref(v_toCommRing_95_);
v___x_96_ = lp_mathlib_Field_toSemifield___redArg(v_inst_89_);
lean_dec_ref(v_inst_89_);
v___x_97_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_96_);
v_toSemiring_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref_n(v_toSemiring_98_, 2);
lean_dec_ref(v___x_97_);
v___x_99_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_98_);
v_toMul_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_toMul_100_);
lean_dec_ref(v___x_99_);
v_toAddCommMonoid_101_ = lean_ctor_get(v_toSemiring_98_, 0);
lean_inc_ref(v_toAddCommMonoid_101_);
lean_dec_ref(v_toSemiring_98_);
v___x_102_ = lean_obj_once(&lp_tree_Formalism_DivisionValues_gramR___redArg___closed__0, &lp_tree_Formalism_DivisionValues_gramR___redArg___closed__0_once, _init_lp_tree_Formalism_DivisionValues_gramR___redArg___closed__0);
v___x_103_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_95_);
v___x_104_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_103_);
v_toFun_105_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_m_92_);
v___x_106_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_106_, 0, v_m_92_);
v___x_107_ = l_List_finRange(v_m_92_);
v___x_108_ = l_List_finRange(v_D_91_);
v___f_109_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_gramR___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_109_, 0, v_e_94_);
lean_closure_set(v___f_109_, 1, v_inst_90_);
lean_closure_set(v___f_109_, 2, v___x_104_);
lean_closure_set(v___f_109_, 3, v___x_108_);
lean_closure_set(v___f_109_, 4, v_00_u0393_93_);
lean_closure_set(v___f_109_, 5, v_toMul_100_);
lean_closure_set(v___f_109_, 6, v_toAddCommMonoid_101_);
lean_inc(v_toFun_105_);
v___x_110_ = lean_apply_1(v_toFun_105_, v___f_109_);
v___x_95__overap_111_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___x_106_, v___x_107_, v_toCommRing_95_);
v___x_112_ = lean_apply_1(v___x_95__overap_111_, v___x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramR(lean_object* v_K_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_D_116_, lean_object* v_m_117_, lean_object* v_00_u0393_118_, lean_object* v_e_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lp_tree_Formalism_DivisionValues_gramR___redArg(v_inst_114_, v_inst_115_, v_D_116_, v_m_117_, v_00_u0393_118_, v_e_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_matLat(lean_object* v_K_121_, lean_object* v_inst_122_, lean_object* v_d_123_, lean_object* v_d_x27_124_, lean_object* v_00_u03c6_125_, lean_object* v_L_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_matLat___boxed(lean_object* v_K_128_, lean_object* v_inst_129_, lean_object* v_d_130_, lean_object* v_d_x27_131_, lean_object* v_00_u03c6_132_, lean_object* v_L_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_tree_Formalism_DivisionValues_matLat(v_K_128_, v_inst_129_, v_d_130_, v_d_x27_131_, v_00_u03c6_132_, v_L_133_);
lean_dec(v_00_u03c6_132_);
lean_dec(v_d_x27_131_);
lean_dec(v_d_130_);
lean_dec_ref(v_inst_129_);
return v_res_134_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_StatementPl(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_Statement(uint8_t builtin) {
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
res = initialize_tree_Formalism_HarderNarasimhan_StatementPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
