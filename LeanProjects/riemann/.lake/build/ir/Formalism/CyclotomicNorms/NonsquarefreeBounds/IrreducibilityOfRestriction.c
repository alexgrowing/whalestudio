// Lean compiler output
// Module: Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.StatementT public import Formalism.GaloisIrreducibility.NoSolvableTransitive public import Lemmata.GeneralBFactSecondBis.Imports
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
uint8_t lp_mathlib_Equiv_Perm_instDecidableRelSameCycle___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Algebra_id___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_instAlgebra___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Module_End_instSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Module_End_instAlgebra___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_toLinAlgEquiv_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AlgEquiv_instFunLike___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_coeHom___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_ofLinearMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Units_coeHom___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_00_u03c3_3_, lean_object* v_i_4_, lean_object* v_a_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lp_mathlib_Equiv_Perm_instDecidableRelSameCycle___redArg(v_inst_1_, v_inst_2_, v_00_u03c3_3_, v_i_4_, v_a_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_00_u03c3_9_, lean_object* v_i_10_, lean_object* v_a_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg___lam__0(v_inst_7_, v_inst_8_, v_00_u03c3_9_, v_i_10_, v_a_11_);
lean_dec(v_inst_8_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_00_u03c3_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___f_18_; lean_object* v___x_19_; 
lean_inc(v_inst_14_);
v___f_18_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_18_, 0, v_inst_15_);
lean_closure_set(v___f_18_, 1, v_inst_14_);
lean_closure_set(v___f_18_, 2, v_00_u03c3_16_);
lean_closure_set(v___f_18_, 3, v_i_17_);
v___x_19_ = lp_mathlib_Multiset_filter___redArg(v___f_18_, v_inst_14_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_00_u03c3_23_, lean_object* v_i_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg(v_inst_21_, v_inst_22_, v_00_u03c3_23_, v_i_24_);
return v___x_25_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__0(lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = l_List_decidablePerm___redArg(v_inst_26_, v_a_27_, v_b_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__0___boxed(lean_object* v_inst_30_, lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__0(v_inst_30_, v_a_31_, v_b_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__1(lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_00_u03c3_37_, lean_object* v_inst_38_, lean_object* v_L_39_, lean_object* v_i_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc___redArg(v_inst_35_, v_inst_36_, v_00_u03c3_37_, v_i_40_);
v___x_42_ = lp_mathlib_Finset_image___redArg(v_inst_38_, v_L_39_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_00_u03c3_46_, lean_object* v_L_47_){
_start:
{
lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
lean_inc_ref(v_inst_45_);
v___f_48_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_48_, 0, v_inst_45_);
lean_inc(v_inst_43_);
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg___lam__1), 6, 5);
lean_closure_set(v___f_49_, 0, v_inst_43_);
lean_closure_set(v___f_49_, 1, v_inst_44_);
lean_closure_set(v___f_49_, 2, v_00_u03c3_46_);
lean_closure_set(v___f_49_, 3, v_inst_45_);
lean_closure_set(v___f_49_, 4, v_L_47_);
v___x_50_ = lp_mathlib_Finset_image___redArg(v___f_48_, v___f_49_, v_inst_43_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks(lean_object* v_00_u03b1_51_, lean_object* v_K_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_00_u03c3_56_, lean_object* v_L_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks___redArg(v_inst_53_, v_inst_54_, v_inst_55_, v_00_u03c3_56_, v_L_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___lam__0(lean_object* v_toAddCommMonoid_59_, lean_object* v_i_60_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_59_);
return v_toAddCommMonoid_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_61_, lean_object* v_i_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___lam__0(v_toAddCommMonoid_61_, v_i_62_);
lean_dec(v_i_62_);
lean_dec_ref(v_toAddCommMonoid_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg(lean_object* v_inst_65_, lean_object* v_N_66_){
_start:
{
lean_object* v___x_67_; lean_object* v_toCommSemiring_68_; lean_object* v_toAddCommMonoid_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_46__overap_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; 
v___x_67_ = lp_mathlib_Field_toSemifield___redArg(v_inst_65_);
v_toCommSemiring_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref_n(v_toCommSemiring_68_, 5);
lean_dec_ref(v___x_67_);
v_toAddCommMonoid_69_ = lean_ctor_get(v_toCommSemiring_68_, 0);
lean_inc(v_N_66_);
v___x_70_ = l_List_finRange(v_N_66_);
v___x_71_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_71_, 0, v_N_66_);
lean_inc_ref(v_toAddCommMonoid_69_);
v___f_72_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_72_, 0, v_toAddCommMonoid_69_);
v___x_73_ = lp_mathlib_Semiring_toModule___redArg(v_toCommSemiring_68_);
v___x_74_ = lp_mathlib_Pi_Function_module___redArg(v___x_73_);
lean_inc_ref_n(v___x_71_, 2);
lean_inc(v___x_70_);
v___x_75_ = lp_mathlib_Matrix_semiring___redArg(v_toCommSemiring_68_, v___x_70_, v___x_71_);
v___x_76_ = lp_mathlib_Algebra_id___redArg(v_toCommSemiring_68_);
v___x_77_ = lp_mathlib_Matrix_instAlgebra___redArg(v___x_71_, v_toCommSemiring_68_, v___x_76_);
v___x_78_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_72_);
v___x_79_ = lp_mathlib_Module_End_instSemiring___redArg(v___x_78_);
v___x_80_ = lp_mathlib_Module_End_instAlgebra___redArg(v___x_74_);
v___x_81_ = lp_mathlib_Matrix_toLinAlgEquiv_x27___redArg(v_toCommSemiring_68_, v___x_71_, v___x_70_);
v___x_46__overap_82_ = lp_mathlib_AlgEquiv_instFunLike___redArg(v_toCommSemiring_68_, v___x_75_, v___x_79_, v___x_77_, v___x_80_);
lean_dec_ref(v___x_80_);
lean_dec_ref(v___x_77_);
lean_dec_ref(v___x_79_);
lean_dec_ref(v___x_75_);
lean_dec_ref(v_toCommSemiring_68_);
v___x_83_ = lean_apply_1(v___x_46__overap_82_, v___x_81_);
v___f_84_ = ((lean_object*)(lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___closed__0));
v___f_85_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_85_, 0, v___f_84_);
lean_closure_set(v___f_85_, 1, v___x_83_);
return v___f_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg___boxed(lean_object* v_inst_86_, lean_object* v_N_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg(v_inst_86_, v_N_87_);
lean_dec_ref(v_inst_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL(lean_object* v_K_89_, lean_object* v_inst_90_, lean_object* v_N_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg(v_inst_90_, v_N_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___boxed(lean_object* v_K_93_, lean_object* v_inst_94_, lean_object* v_N_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL(v_K_93_, v_inst_94_, v_N_95_);
lean_dec_ref(v_inst_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___redArg(lean_object* v_inst_97_, lean_object* v_N_98_, lean_object* v_A_99_){
_start:
{
lean_object* v_val_100_; lean_object* v_inv_101_; lean_object* v___x_41__overap_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_52__overap_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_val_100_ = lean_ctor_get(v_A_99_, 0);
lean_inc(v_val_100_);
v_inv_101_ = lean_ctor_get(v_A_99_, 1);
lean_inc(v_inv_101_);
lean_inc(v_N_98_);
v___x_41__overap_102_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg(v_inst_97_, v_N_98_);
v___x_103_ = lean_apply_1(v___x_41__overap_102_, v_A_99_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_inv_101_);
lean_ctor_set(v___x_104_, 1, v_val_100_);
v___x_52__overap_105_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL___redArg(v_inst_97_, v_N_98_);
v___x_106_ = lean_apply_1(v___x_52__overap_105_, v___x_104_);
v___x_107_ = lp_mathlib_LinearEquiv_ofLinearMap___redArg(v___x_103_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___redArg___boxed(lean_object* v_inst_108_, lean_object* v_N_109_, lean_object* v_A_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___redArg(v_inst_108_, v_N_109_, v_A_110_);
lean_dec_ref(v_inst_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv(lean_object* v_K_112_, lean_object* v_inst_113_, lean_object* v_N_114_, lean_object* v_A_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___redArg(v_inst_113_, v_N_114_, v_A_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv___boxed(lean_object* v_K_117_, lean_object* v_inst_118_, lean_object* v_N_119_, lean_object* v_A_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv(v_K_117_, v_inst_118_, v_N_119_, v_A_120_);
lean_dec_ref(v_inst_118_);
return v_res_121_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementT(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_NoSolvableTransitive(uint8_t builtin);
lean_object* initialize_tree_Lemmata_GeneralBFactSecondBis_Imports(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_StatementT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_NoSolvableTransitive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_GeneralBFactSecondBis_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
