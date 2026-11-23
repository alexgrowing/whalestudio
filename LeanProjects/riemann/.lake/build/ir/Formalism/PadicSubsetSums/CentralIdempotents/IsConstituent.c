// Lean compiler output
// Module: Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_parab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_parab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcSpace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_Intw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_Intw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_ggSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_ggSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_parab(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_00_u03b9_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_s_8_, lean_object* v_b_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_parab___boxed(lean_object* v_K_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03b9_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_s_18_, lean_object* v_b_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_parab(v_K_11_, v_inst_12_, v_inst_13_, v_inst_14_, v_00_u03b9_15_, v_inst_16_, v_inst_17_, v_s_18_, v_b_19_);
lean_dec_ref(v_b_19_);
lean_dec(v_s_18_);
lean_dec_ref(v_inst_17_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_14_);
lean_dec(v_inst_13_);
lean_dec_ref(v_inst_12_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___lam__0(lean_object* v_self_21_){
_start:
{
lean_inc(v_self_21_);
return v_self_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___lam__0___boxed(lean_object* v_self_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___lam__0(v_self_22_);
lean_dec(v_self_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg(lean_object* v_M_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = ((lean_object*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg___closed__0));
v___x_29_ = lp_mathlib_Matrix_submatrix___redArg(v_M_25_, v___f_28_, v___f_28_, v_a_26_, v_a_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk(lean_object* v_K_30_, lean_object* v_00_u03b9_31_, lean_object* v_s_32_, lean_object* v_b_33_, lean_object* v_c_34_, lean_object* v_M_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___redArg(v_M_35_, v_a_36_, v_a_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___boxed(lean_object* v_K_39_, lean_object* v_00_u03b9_40_, lean_object* v_s_41_, lean_object* v_b_42_, lean_object* v_c_43_, lean_object* v_M_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk(v_K_39_, v_00_u03b9_40_, v_s_41_, v_b_42_, v_c_43_, v_M_44_, v_a_45_, v_a_46_);
lean_dec(v_c_43_);
lean_dec_ref(v_b_42_);
lean_dec(v_s_41_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi___redArg(lean_object* v_s_48_, lean_object* v_b_49_, lean_object* v_c_50_, lean_object* v_p_51_){
_start:
{
lean_object* v_val_52_; lean_object* v_inv_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_62_; 
v_val_52_ = lean_ctor_get(v_p_51_, 0);
v_inv_53_ = lean_ctor_get(v_p_51_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_p_51_);
if (v_isSharedCheck_62_ == 0)
{
v___x_55_ = v_p_51_;
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_inv_53_);
lean_inc(v_val_52_);
lean_dec(v_p_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
lean_inc(v_c_50_);
lean_inc_ref(v_b_49_);
lean_inc(v_s_48_);
v___x_57_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___boxed), 8, 6);
lean_closure_set(v___x_57_, 0, lean_box(0));
lean_closure_set(v___x_57_, 1, lean_box(0));
lean_closure_set(v___x_57_, 2, v_s_48_);
lean_closure_set(v___x_57_, 3, v_b_49_);
lean_closure_set(v___x_57_, 4, v_c_50_);
lean_closure_set(v___x_57_, 5, v_val_52_);
v___x_58_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_blk___boxed), 8, 6);
lean_closure_set(v___x_58_, 0, lean_box(0));
lean_closure_set(v___x_58_, 1, lean_box(0));
lean_closure_set(v___x_58_, 2, v_s_48_);
lean_closure_set(v___x_58_, 3, v_b_49_);
lean_closure_set(v___x_58_, 4, v_c_50_);
lean_closure_set(v___x_58_, 5, v_inv_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_58_);
lean_ctor_set(v___x_55_, 0, v___x_57_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi(lean_object* v_K_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_00_u03b9_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_s_70_, lean_object* v_b_71_, lean_object* v_c_72_, lean_object* v_p_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi___redArg(v_s_70_, v_b_71_, v_c_72_, v_p_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi___boxed(lean_object* v_K_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_00_u03b9_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_s_82_, lean_object* v_b_83_, lean_object* v_c_84_, lean_object* v_p_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_levi(v_K_75_, v_inst_76_, v_inst_77_, v_inst_78_, v_00_u03b9_79_, v_inst_80_, v_inst_81_, v_s_82_, v_b_83_, v_c_84_, v_p_85_);
lean_dec_ref(v_inst_81_);
lean_dec(v_inst_80_);
lean_dec_ref(v_inst_78_);
lean_dec(v_inst_77_);
lean_dec_ref(v_inst_76_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcSpace(lean_object* v_K_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_00_u03b9_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_s_94_, lean_object* v_b_95_, lean_object* v_lam_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_box(0);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcSpace___boxed(lean_object* v_K_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_00_u03b9_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_s_105_, lean_object* v_b_106_, lean_object* v_lam_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcSpace(v_K_98_, v_inst_99_, v_inst_100_, v_inst_101_, v_00_u03b9_102_, v_inst_103_, v_inst_104_, v_s_105_, v_b_106_, v_lam_107_);
lean_dec_ref(v_lam_107_);
lean_dec_ref(v_b_106_);
lean_dec(v_s_105_);
lean_dec_ref(v_inst_104_);
lean_dec(v_inst_103_);
lean_dec_ref(v_inst_101_);
lean_dec(v_inst_100_);
lean_dec_ref(v_inst_99_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__0(lean_object* v_inv_109_, lean_object* v___y_110_, lean_object* v_j_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_apply_2(v_inv_109_, v_j_111_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__1(lean_object* v_inv_113_, lean_object* v___y_114_, lean_object* v_j_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_apply_2(v_inv_113_, v___y_114_, v_j_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__2(lean_object* v_inv_117_, lean_object* v_inv_118_, lean_object* v_inst_119_, lean_object* v_toMul_120_, lean_object* v_toAddCommMonoid_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___x_126_; 
v___f_124_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__0), 3, 2);
lean_closure_set(v___f_124_, 0, v_inv_117_);
lean_closure_set(v___f_124_, 1, v___y_123_);
v___f_125_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__1), 3, 2);
lean_closure_set(v___f_125_, 0, v_inv_118_);
lean_closure_set(v___f_125_, 1, v___y_122_);
v___x_126_ = lp_mathlib_dotProduct___redArg(v_inst_119_, v_toMul_120_, v_toAddCommMonoid_121_, v___f_125_, v___f_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__2___boxed(lean_object* v_inv_127_, lean_object* v_inv_128_, lean_object* v_inst_129_, lean_object* v_toMul_130_, lean_object* v_toAddCommMonoid_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__2(v_inv_127_, v_inv_128_, v_inst_129_, v_toMul_130_, v_toAddCommMonoid_131_, v___y_132_, v___y_133_);
lean_dec_ref(v_toAddCommMonoid_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__3(lean_object* v_val_135_, lean_object* v___y_136_, lean_object* v_j_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_apply_2(v_val_135_, v_j_137_, v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__4(lean_object* v_val_139_, lean_object* v___y_140_, lean_object* v_j_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_2(v_val_139_, v___y_140_, v_j_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__5(lean_object* v_val_143_, lean_object* v_val_144_, lean_object* v_inst_145_, lean_object* v_toMul_146_, lean_object* v_toAddCommMonoid_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___x_152_; 
v___f_150_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__3), 3, 2);
lean_closure_set(v___f_150_, 0, v_val_143_);
lean_closure_set(v___f_150_, 1, v___y_149_);
v___f_151_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__4), 3, 2);
lean_closure_set(v___f_151_, 0, v_val_144_);
lean_closure_set(v___f_151_, 1, v___y_148_);
v___x_152_ = lp_mathlib_dotProduct___redArg(v_inst_145_, v_toMul_146_, v_toAddCommMonoid_147_, v___f_151_, v___f_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__5___boxed(lean_object* v_val_153_, lean_object* v_val_154_, lean_object* v_inst_155_, lean_object* v_toMul_156_, lean_object* v_toAddCommMonoid_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__5(v_val_153_, v_val_154_, v_inst_155_, v_toMul_156_, v_toAddCommMonoid_157_, v___y_158_, v___y_159_);
lean_dec_ref(v_toAddCommMonoid_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__6(lean_object* v_toSemiring_161_, lean_object* v_inst_162_, lean_object* v_g_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_val_166_; lean_object* v_inv_167_; lean_object* v_val_168_; lean_object* v_inv_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_183_; 
v_val_166_ = lean_ctor_get(v___y_165_, 0);
lean_inc(v_val_166_);
v_inv_167_ = lean_ctor_get(v___y_165_, 1);
lean_inc(v_inv_167_);
lean_dec_ref(v___y_165_);
v_val_168_ = lean_ctor_get(v_g_163_, 0);
v_inv_169_ = lean_ctor_get(v_g_163_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_g_163_);
if (v_isSharedCheck_183_ == 0)
{
v___x_171_ = v_g_163_;
v_isShared_172_ = v_isSharedCheck_183_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_inv_169_);
lean_inc(v_val_168_);
lean_dec(v_g_163_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_183_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v_toAddCommMonoid_174_; lean_object* v___x_175_; lean_object* v_toMul_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_180_; 
v___x_173_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_161_);
v_toAddCommMonoid_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref_n(v_toAddCommMonoid_174_, 2);
v___x_175_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_173_);
v_toMul_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc_n(v_toMul_176_, 2);
lean_dec_ref(v___x_175_);
lean_inc(v_inst_162_);
v___f_177_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_177_, 0, v_inv_167_);
lean_closure_set(v___f_177_, 1, v_inv_169_);
lean_closure_set(v___f_177_, 2, v_inst_162_);
lean_closure_set(v___f_177_, 3, v_toMul_176_);
lean_closure_set(v___f_177_, 4, v_toAddCommMonoid_174_);
v___f_178_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_178_, 0, v_val_168_);
lean_closure_set(v___f_178_, 1, v_val_166_);
lean_closure_set(v___f_178_, 2, v_inst_162_);
lean_closure_set(v___f_178_, 3, v_toMul_176_);
lean_closure_set(v___f_178_, 4, v_toAddCommMonoid_174_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___f_177_);
lean_ctor_set(v___x_171_, 0, v___f_178_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___f_178_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___f_177_);
v___x_180_ = v_reuseFailAlloc_182_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; 
v___x_181_ = lean_apply_1(v___y_164_, v___x_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__6___boxed(lean_object* v_toSemiring_184_, lean_object* v_inst_185_, lean_object* v_g_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__6(v_toSemiring_184_, v_inst_185_, v_g_186_, v___y_187_, v___y_188_);
lean_dec_ref(v_toSemiring_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg(lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_toSemiring_194_; lean_object* v___f_195_; 
v___x_192_ = lp_mathlib_Field_toSemifield___redArg(v_inst_190_);
v___x_193_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_192_);
v_toSemiring_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc_ref(v_toSemiring_194_);
lean_dec_ref(v___x_193_);
v___f_195_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_195_, 0, v_toSemiring_194_);
lean_closure_set(v___f_195_, 1, v_inst_191_);
return v___f_195_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg___boxed(lean_object* v_inst_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg(v_inst_196_, v_inst_197_);
lean_dec_ref(v_inst_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep(lean_object* v_K_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_00_u03b9_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_s_206_, lean_object* v_b_207_, lean_object* v_lam_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___redArg(v_inst_200_, v_inst_204_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep___boxed(lean_object* v_K_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_00_u03b9_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_s_217_, lean_object* v_b_218_, lean_object* v_lam_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_hcRep(v_K_210_, v_inst_211_, v_inst_212_, v_inst_213_, v_00_u03b9_214_, v_inst_215_, v_inst_216_, v_s_217_, v_b_218_, v_lam_219_);
lean_dec_ref(v_lam_219_);
lean_dec_ref(v_b_218_);
lean_dec(v_s_217_);
lean_dec_ref(v_inst_216_);
lean_dec_ref(v_inst_213_);
lean_dec(v_inst_212_);
lean_dec_ref(v_inst_211_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_Intw(lean_object* v_00_u0393_221_, lean_object* v_inst_222_, lean_object* v_V_223_, lean_object* v_V_x27_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_00_u03c1_229_, lean_object* v_00_u03c1_x27_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_Intw___boxed(lean_object* v_00_u0393_232_, lean_object* v_inst_233_, lean_object* v_V_234_, lean_object* v_V_x27_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_00_u03c1_240_, lean_object* v_00_u03c1_x27_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_Intw(v_00_u0393_232_, v_inst_233_, v_V_234_, v_V_x27_235_, v_inst_236_, v_inst_237_, v_inst_238_, v_inst_239_, v_00_u03c1_240_, v_00_u03c1_x27_241_);
lean_dec(v_00_u03c1_x27_241_);
lean_dec(v_00_u03c1_240_);
lean_dec(v_inst_239_);
lean_dec_ref(v_inst_238_);
lean_dec(v_inst_237_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_233_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___redArg(lean_object* v_inst_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_List_lengthTR___redArg(v_inst_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___redArg___boxed(lean_object* v_inst_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___redArg(v_inst_245_);
lean_dec(v_inst_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q(lean_object* v_K_247_, lean_object* v_inst_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_List_lengthTR___redArg(v_inst_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q___boxed(lean_object* v_K_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_q(v_K_250_, v_inst_251_);
lean_dec(v_inst_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__0(lean_object* v_i_253_, lean_object* v_toSemiring_254_, lean_object* v_u_255_, lean_object* v_j_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_253_, v___x_257_);
v___x_259_ = lean_nat_dec_eq(v_j_256_, v___x_258_);
lean_dec(v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v_toZero_261_; 
lean_dec(v_j_256_);
lean_dec_ref(v_u_255_);
lean_dec(v_i_253_);
v___x_260_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_254_);
v_toZero_261_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_toZero_261_);
lean_dec_ref(v___x_260_);
return v_toZero_261_;
}
else
{
lean_object* v_val_262_; lean_object* v___x_263_; 
lean_dec_ref(v_toSemiring_254_);
v_val_262_ = lean_ctor_get(v_u_255_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v_u_255_);
v___x_263_ = lean_apply_2(v_val_262_, v_i_253_, v_j_256_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__1(lean_object* v_toSemiring_264_, lean_object* v_u_265_, lean_object* v_toAddCommMonoid_266_, lean_object* v___x_267_, lean_object* v_i_268_){
_start:
{
lean_object* v___f_269_; lean_object* v___x_270_; 
v___f_269_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__0), 4, 3);
lean_closure_set(v___f_269_, 0, v_i_268_);
lean_closure_set(v___f_269_, 1, v_toSemiring_264_);
lean_closure_set(v___f_269_, 2, v_u_265_);
v___x_270_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_266_, v___x_267_, v___f_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__1___boxed(lean_object* v_toSemiring_271_, lean_object* v_u_272_, lean_object* v_toAddCommMonoid_273_, lean_object* v___x_274_, lean_object* v_i_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__1(v_toSemiring_271_, v_u_272_, v_toAddCommMonoid_273_, v___x_274_, v_i_275_);
lean_dec_ref(v_toAddCommMonoid_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg(lean_object* v_inst_277_, lean_object* v_n_278_, lean_object* v_00_u03c8_u2080_279_, lean_object* v_u_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_toSemiring_283_; lean_object* v_toAddCommMonoid_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_281_ = lp_mathlib_Field_toSemifield___redArg(v_inst_277_);
v___x_282_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_281_);
v_toSemiring_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_toSemiring_283_);
lean_dec_ref(v___x_282_);
v_toAddCommMonoid_284_ = lean_ctor_get(v_toSemiring_283_, 0);
lean_inc_ref_n(v_toAddCommMonoid_284_, 2);
v___x_285_ = l_List_finRange(v_n_278_);
lean_inc(v___x_285_);
v___f_286_ = lean_alloc_closure((void*)(lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_286_, 0, v_toSemiring_283_);
lean_closure_set(v___f_286_, 1, v_u_280_);
lean_closure_set(v___f_286_, 2, v_toAddCommMonoid_284_);
lean_closure_set(v___f_286_, 3, v___x_285_);
v___x_287_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_284_, v___x_285_, v___f_286_);
lean_dec_ref(v_toAddCommMonoid_284_);
v___x_288_ = lean_apply_1(v_00_u03c8_u2080_279_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg___boxed(lean_object* v_inst_289_, lean_object* v_n_290_, lean_object* v_00_u03c8_u2080_291_, lean_object* v_u_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg(v_inst_289_, v_n_290_, v_00_u03c8_u2080_291_, v_u_292_);
lean_dec_ref(v_inst_289_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU(lean_object* v_K_294_, lean_object* v_inst_295_, lean_object* v_n_296_, lean_object* v_00_u03c8_u2080_297_, lean_object* v_u_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___redArg(v_inst_295_, v_n_296_, v_00_u03c8_u2080_297_, v_u_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU___boxed(lean_object* v_K_300_, lean_object* v_inst_301_, lean_object* v_n_302_, lean_object* v_00_u03c8_u2080_303_, lean_object* v_u_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_psiU(v_K_300_, v_inst_301_, v_n_302_, v_00_u03c8_u2080_303_, v_u_304_);
lean_dec_ref(v_inst_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_ggSub(lean_object* v_K_306_, lean_object* v_inst_307_, lean_object* v_n_308_, lean_object* v_V_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_00_u03c8_u2080_312_, lean_object* v_00_u03c1_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(0);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_ggSub___boxed(lean_object* v_K_315_, lean_object* v_inst_316_, lean_object* v_n_317_, lean_object* v_V_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_00_u03c8_u2080_321_, lean_object* v_00_u03c1_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = lp_tree_Formalism_IrreducibleCountingLemmas_TYPES_ggSub(v_K_315_, v_inst_316_, v_n_317_, v_V_318_, v_inst_319_, v_inst_320_, v_00_u03c8_u2080_321_, v_00_u03c1_322_);
lean_dec(v_00_u03c1_322_);
lean_dec_ref(v_00_u03c8_u2080_321_);
lean_dec(v_inst_320_);
lean_dec_ref(v_inst_319_);
lean_dec(v_n_317_);
lean_dec_ref(v_inst_316_);
return v_res_323_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
