// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.StatementE
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementB
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_Perm_signAux2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instNatCast___lam__0(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Equiv_instFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Tm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Tm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Tm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_REAL_qdet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_REAL_qdet___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_REAL_qdet___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qdet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qdet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Tm___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_E_3_, lean_object* v_u_4_, lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
lean_object* v_toSemiring_7_; lean_object* v___x_8_; lean_object* v_toAdd_9_; lean_object* v___y_11_; uint8_t v___x_14_; 
v_toSemiring_7_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref_n(v_toSemiring_7_, 2);
lean_dec_ref(v_inst_1_);
v___x_8_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_7_);
v_toAdd_9_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_toAdd_9_);
lean_dec_ref(v___x_8_);
v___x_14_ = lean_nat_dec_eq(v_a_5_, v_b_6_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v_toZero_16_; 
lean_dec_ref(v_u_4_);
lean_dec_ref(v_inst_2_);
v___x_15_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_7_);
v_toZero_16_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_toZero_16_);
lean_dec_ref(v___x_15_);
v___y_11_ = v_toZero_16_;
goto v___jp_10_;
}
else
{
lean_object* v_algebraMap_17_; lean_object* v___x_18_; 
lean_dec_ref(v_toSemiring_7_);
v_algebraMap_17_ = lean_ctor_get(v_inst_2_, 1);
lean_inc(v_algebraMap_17_);
lean_dec_ref(v_inst_2_);
v___x_18_ = lean_apply_1(v_algebraMap_17_, v_u_4_);
v___y_11_ = v___x_18_;
goto v___jp_10_;
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_apply_2(v_E_3_, v_a_5_, v_b_6_);
v___x_13_ = lean_apply_2(v_toAdd_9_, v___y_11_, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Tm(lean_object* v_A_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_n_22_, lean_object* v_E_23_, lean_object* v_u_24_, lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_REAL_Tm___redArg(v_inst_20_, v_inst_21_, v_E_23_, v_u_24_, v_a_25_, v_b_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Tm___boxed(lean_object* v_A_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_n_31_, lean_object* v_E_32_, lean_object* v_u_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_REAL_Tm(v_A_28_, v_inst_29_, v_inst_30_, v_n_31_, v_E_32_, v_u_33_, v_a_34_, v_b_35_);
lean_dec(v_n_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg___lam__0(lean_object* v_u_37_, lean_object* v_00_u03c3_38_, lean_object* v_a_39_, lean_object* v_b_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_E_43_, lean_object* v_k_44_){
_start:
{
lean_object* v_re_45_; lean_object* v_im_46_; lean_object* v___x_47_; lean_object* v_re_48_; lean_object* v_im_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_65_; 
v_re_45_ = lean_ctor_get(v_u_37_, 0);
lean_inc(v_re_45_);
v_im_46_ = lean_ctor_get(v_u_37_, 1);
lean_inc(v_im_46_);
lean_dec_ref(v_u_37_);
lean_inc(v_k_44_);
v___x_47_ = lp_mathlib_Complex_instNatCast___lam__0(v_k_44_);
v_re_48_ = lean_ctor_get(v___x_47_, 0);
v_im_49_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_65_ == 0)
{
v___x_51_ = v___x_47_;
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_im_49_);
lean_inc(v_re_48_);
lean_dec(v___x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_toFun_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_59_; 
v_toFun_53_ = lean_ctor_get(v_00_u03c3_38_, 0);
lean_inc(v_toFun_53_);
lean_dec_ref(v_00_u03c3_38_);
v___f_54_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_54_, 0, v_re_48_);
v___f_55_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_55_, 0, v_re_45_);
lean_closure_set(v___f_55_, 1, v___f_54_);
v___f_56_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_56_, 0, v_im_49_);
v___f_57_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_57_, 0, v_im_46_);
lean_closure_set(v___f_57_, 1, v___f_56_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___f_57_);
lean_ctor_set(v___x_51_, 0, v___f_55_);
v___x_59_ = v___x_51_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___f_55_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___f_57_);
v___x_59_ = v_reuseFailAlloc_64_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_inc(v_k_44_);
v___x_60_ = lean_apply_1(v_toFun_53_, v_k_44_);
v___x_61_ = lean_apply_1(v_a_39_, v___x_60_);
v___x_62_ = lean_apply_1(v_b_40_, v_k_44_);
v___x_63_ = lp_tree_Formalism_REAL_Tm___redArg(v_inst_41_, v_inst_42_, v_E_43_, v___x_59_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg___lam__1(lean_object* v___x_66_, lean_object* v___x_67_, lean_object* v_u_68_, lean_object* v_a_69_, lean_object* v_b_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_E_73_, lean_object* v_toIntCast_74_, lean_object* v_t_75_, lean_object* v_toMul_76_, lean_object* v_toOne_77_, lean_object* v_00_u03c3_78_){
_start:
{
lean_object* v___x_79_; lean_object* v_val_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_inc_ref(v_00_u03c3_78_);
v___x_79_ = lp_mathlib_Equiv_Perm_signAux2___redArg(v___x_66_, v___x_67_, v_00_u03c3_78_);
v_val_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_80_);
lean_dec_ref(v___x_79_);
v___f_81_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_qminor___redArg___lam__0), 8, 7);
lean_closure_set(v___f_81_, 0, v_u_68_);
lean_closure_set(v___f_81_, 1, v_00_u03c3_78_);
lean_closure_set(v___f_81_, 2, v_a_69_);
lean_closure_set(v___f_81_, 3, v_b_70_);
lean_closure_set(v___f_81_, 4, v_inst_71_);
lean_closure_set(v___f_81_, 5, v_inst_72_);
lean_closure_set(v___f_81_, 6, v_E_73_);
v___x_82_ = lean_apply_1(v_toIntCast_74_, v_val_80_);
v___x_83_ = l_List_ofFn___redArg(v_t_75_, v___f_81_);
lean_inc(v_toMul_76_);
v___x_84_ = l_List_prod___redArg(v_toMul_76_, v_toOne_77_, v___x_83_);
v___x_85_ = lean_apply_2(v_toMul_76_, v___x_82_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg___lam__1___boxed(lean_object* v___x_86_, lean_object* v___x_87_, lean_object* v_u_88_, lean_object* v_a_89_, lean_object* v_b_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_E_93_, lean_object* v_toIntCast_94_, lean_object* v_t_95_, lean_object* v_toMul_96_, lean_object* v_toOne_97_, lean_object* v_00_u03c3_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_tree_Formalism_REAL_qminor___redArg___lam__1(v___x_86_, v___x_87_, v_u_88_, v_a_89_, v_b_90_, v_inst_91_, v_inst_92_, v_E_93_, v_toIntCast_94_, v_t_95_, v_toMul_96_, v_toOne_97_, v_00_u03c3_98_);
lean_dec(v_toOne_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___redArg(lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_t_102_, lean_object* v_E_103_, lean_object* v_a_104_, lean_object* v_b_105_, lean_object* v_u_106_){
_start:
{
lean_object* v_toSemiring_107_; lean_object* v_toAddCommMonoid_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_toMul_113_; lean_object* v___x_114_; lean_object* v_toAddMonoidWithOne_115_; lean_object* v_toIntCast_116_; lean_object* v_toOne_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_toSemiring_107_ = lean_ctor_get(v_inst_100_, 0);
v_toAddCommMonoid_108_ = lean_ctor_get(v_toSemiring_107_, 0);
lean_inc_ref(v_toAddCommMonoid_108_);
lean_inc_n(v_t_102_, 2);
v___x_109_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_109_, 0, v_t_102_);
v___x_110_ = l_List_finRange(v_t_102_);
lean_inc_n(v___x_110_, 2);
lean_inc_ref_n(v___x_109_, 2);
v___x_111_ = lp_mathlib_Equiv_instFintype___redArg(v___x_109_, v___x_109_, v___x_110_, v___x_110_);
lean_inc_ref(v_toSemiring_107_);
v___x_112_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_107_);
v_toMul_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_toMul_113_);
lean_dec_ref(v___x_112_);
lean_inc_ref(v_inst_100_);
v___x_114_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_100_);
v_toAddMonoidWithOne_115_ = lean_ctor_get(v___x_114_, 1);
lean_inc_ref(v_toAddMonoidWithOne_115_);
v_toIntCast_116_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_toIntCast_116_);
lean_dec_ref(v___x_114_);
v_toOne_117_ = lean_ctor_get(v_toAddMonoidWithOne_115_, 2);
lean_inc(v_toOne_117_);
lean_dec_ref(v_toAddMonoidWithOne_115_);
v___f_118_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_qminor___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_118_, 0, v___x_109_);
lean_closure_set(v___f_118_, 1, v___x_110_);
lean_closure_set(v___f_118_, 2, v_u_106_);
lean_closure_set(v___f_118_, 3, v_a_104_);
lean_closure_set(v___f_118_, 4, v_b_105_);
lean_closure_set(v___f_118_, 5, v_inst_100_);
lean_closure_set(v___f_118_, 6, v_inst_101_);
lean_closure_set(v___f_118_, 7, v_E_103_);
lean_closure_set(v___f_118_, 8, v_toIntCast_116_);
lean_closure_set(v___f_118_, 9, v_t_102_);
lean_closure_set(v___f_118_, 10, v_toMul_113_);
lean_closure_set(v___f_118_, 11, v_toOne_117_);
v___x_119_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_108_, v___x_111_, v___f_118_);
lean_dec_ref(v_toAddCommMonoid_108_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor(lean_object* v_A_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_n_123_, lean_object* v_t_124_, lean_object* v_E_125_, lean_object* v_a_126_, lean_object* v_b_127_, lean_object* v_u_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_tree_Formalism_REAL_qminor___redArg(v_inst_121_, v_inst_122_, v_t_124_, v_E_125_, v_a_126_, v_b_127_, v_u_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qminor___boxed(lean_object* v_A_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_n_133_, lean_object* v_t_134_, lean_object* v_E_135_, lean_object* v_a_136_, lean_object* v_b_137_, lean_object* v_u_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_tree_Formalism_REAL_qminor(v_A_130_, v_inst_131_, v_inst_132_, v_n_133_, v_t_134_, v_E_135_, v_a_136_, v_b_137_, v_u_138_);
lean_dec(v_n_133_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qdet___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_n_143_, lean_object* v_E_144_, lean_object* v_u_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(lp_tree_Formalism_REAL_qdet___redArg___closed__0));
v___x_147_ = lp_tree_Formalism_REAL_qminor___redArg(v_inst_141_, v_inst_142_, v_n_143_, v_E_144_, v___x_146_, v___x_146_, v_u_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_qdet(lean_object* v_A_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_n_151_, lean_object* v_E_152_, lean_object* v_u_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lp_tree_Formalism_REAL_qdet___redArg(v_inst_149_, v_inst_150_, v_n_151_, v_E_152_, v_u_153_);
return v___x_154_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementE(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
