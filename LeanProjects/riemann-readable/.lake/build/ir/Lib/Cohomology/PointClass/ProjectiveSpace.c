// Lean compiler output
// Module: Lib.Cohomology.PointClass.ProjectiveSpace
// Imports: public import Init public meta import Init public import Lib.Cohomology.PointClass.NoetherNormalization public import Lib.PadicComparison.Primitive.PeriodCoefficients
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_cons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_affineSpace___redArg();
lean_object* lp_mathlib_CategoryTheory_Subfunctor_toFunctor___redArg(lean_object*);
lean_object* lp_mathlib_Fin_insertNth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_projSpace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_projSpace___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_projSpace___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_projSpace___redArg___closed__0_value;
static const lean_ctor_object lp_GRH_New_Variety_projSpace___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Variety_projSpace___redArg___closed__0_value)}};
static const lean_object* lp_GRH_New_Variety_projSpace___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Variety_projSpace___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_projSpace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_projSpace___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_affinePoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_affinePoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_affinePoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg___lam__0(lean_object* v_map_1_, lean_object* v_X_2_, lean_object* v_Y_3_, lean_object* v_f_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_apply_5(v_map_1_, v_X_2_, v_Y_3_, v_f_4_, v___y_5_, v___y_6_);
return v___x_7_;
}
}
static lean_object* _init_lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_GRH_New_Variety_affineSpace___redArg();
return v___x_8_;
}
}
static lean_object* _init_lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__0, &lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__0_once, _init_lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__0);
v___x_10_ = lp_mathlib_CategoryTheory_Subfunctor_toFunctor___redArg(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg___lam__1(lean_object* v_X_11_, lean_object* v_Y_12_, lean_object* v_f_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_map_16_; lean_object* v___f_17_; 
v___x_15_ = lean_obj_once(&lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__1, &lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__1_once, _init_lp_GRH_New_Variety_projSpace___redArg___lam__1___closed__1);
v_map_16_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_map_16_);
v___f_17_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_projSpace___redArg___lam__0), 6, 5);
lean_closure_set(v___f_17_, 0, v_map_16_);
lean_closure_set(v___f_17_, 1, v_X_11_);
lean_closure_set(v___f_17_, 2, v_Y_12_);
lean_closure_set(v___f_17_, 3, v_f_13_);
lean_closure_set(v___f_17_, 4, v___y_14_);
return v___f_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg(){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = ((lean_object*)(lp_GRH_New_Variety_projSpace___redArg___closed__1));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___redArg___boxed(lean_object* v___dummy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_Variety_projSpace___redArg();
return v_res_24_;
}
}
static lean_object* _init_lp_GRH_New_Variety_projSpace___closed__0(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_GRH_New_Variety_projSpace___redArg();
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace(lean_object* v_k_26_, lean_object* v_inst_27_, lean_object* v_d_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_obj_once(&lp_GRH_New_Variety_projSpace___closed__0, &lp_GRH_New_Variety_projSpace___closed__0_once, _init_lp_GRH_New_Variety_projSpace___closed__0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace___boxed(lean_object* v_k_30_, lean_object* v_inst_31_, lean_object* v_d_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_Variety_projSpace(v_k_30_, v_inst_31_, v_d_32_);
lean_dec(v_d_32_);
lean_dec_ref(v_inst_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk___redArg(lean_object* v_v_34_){
_start:
{
lean_inc(v_v_34_);
return v_v_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk___redArg___boxed(lean_object* v_v_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_Variety_projSpace_mk___redArg(v_v_35_);
lean_dec(v_v_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk(lean_object* v_k_37_, lean_object* v_inst_38_, lean_object* v_d_39_, lean_object* v_A_40_, lean_object* v_v_41_, lean_object* v_h_42_){
_start:
{
lean_inc(v_v_41_);
return v_v_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_mk___boxed(lean_object* v_k_43_, lean_object* v_inst_44_, lean_object* v_d_45_, lean_object* v_A_46_, lean_object* v_v_47_, lean_object* v_h_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH_New_Variety_projSpace_mk(v_k_43_, v_inst_44_, v_d_45_, v_A_46_, v_v_47_, v_h_48_);
lean_dec(v_v_47_);
lean_dec_ref(v_A_46_);
lean_dec(v_d_45_);
lean_dec_ref(v_inst_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_affinePoint___redArg(lean_object* v_d_50_, lean_object* v_A_51_, lean_object* v_i_52_, lean_object* v_v_53_){
_start:
{
lean_object* v_commRing_54_; lean_object* v___x_55_; lean_object* v_toAddMonoidWithOne_56_; lean_object* v_toOne_57_; lean_object* v___x_58_; 
v_commRing_54_ = lean_ctor_get(v_A_51_, 0);
lean_inc_ref(v_commRing_54_);
lean_dec_ref(v_A_51_);
v___x_55_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_commRing_54_);
v_toAddMonoidWithOne_56_ = lean_ctor_get(v___x_55_, 1);
lean_inc_ref(v_toAddMonoidWithOne_56_);
lean_dec_ref(v___x_55_);
v_toOne_57_ = lean_ctor_get(v_toAddMonoidWithOne_56_, 2);
lean_inc(v_toOne_57_);
lean_dec_ref(v_toAddMonoidWithOne_56_);
v___x_58_ = lean_alloc_closure((void*)(lp_mathlib_Fin_insertNth___boxed), 6, 5);
lean_closure_set(v___x_58_, 0, v_d_50_);
lean_closure_set(v___x_58_, 1, lean_box(0));
lean_closure_set(v___x_58_, 2, v_i_52_);
lean_closure_set(v___x_58_, 3, v_toOne_57_);
lean_closure_set(v___x_58_, 4, v_v_53_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_affinePoint(lean_object* v_k_59_, lean_object* v_inst_60_, lean_object* v_d_61_, lean_object* v_A_62_, lean_object* v_i_63_, lean_object* v_v_64_){
_start:
{
lean_object* v_commRing_65_; lean_object* v___x_66_; lean_object* v_toAddMonoidWithOne_67_; lean_object* v_toOne_68_; lean_object* v___x_69_; 
v_commRing_65_ = lean_ctor_get(v_A_62_, 0);
lean_inc_ref(v_commRing_65_);
lean_dec_ref(v_A_62_);
v___x_66_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_commRing_65_);
v_toAddMonoidWithOne_67_ = lean_ctor_get(v___x_66_, 1);
lean_inc_ref(v_toAddMonoidWithOne_67_);
lean_dec_ref(v___x_66_);
v_toOne_68_ = lean_ctor_get(v_toAddMonoidWithOne_67_, 2);
lean_inc(v_toOne_68_);
lean_dec_ref(v_toAddMonoidWithOne_67_);
v___x_69_ = lean_alloc_closure((void*)(lp_mathlib_Fin_insertNth___boxed), 6, 5);
lean_closure_set(v___x_69_, 0, v_d_61_);
lean_closure_set(v___x_69_, 1, lean_box(0));
lean_closure_set(v___x_69_, 2, v_i_63_);
lean_closure_set(v___x_69_, 3, v_toOne_68_);
lean_closure_set(v___x_69_, 4, v_v_64_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_affinePoint___boxed(lean_object* v_k_70_, lean_object* v_inst_71_, lean_object* v_d_72_, lean_object* v_A_73_, lean_object* v_i_74_, lean_object* v_v_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_Variety_projSpace_affinePoint(v_k_70_, v_inst_71_, v_d_72_, v_A_73_, v_i_74_, v_v_75_);
lean_dec_ref(v_inst_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__0(lean_object* v_fst_77_, lean_object* v_i_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_1(v_fst_77_, v_i_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__1(lean_object* v___x_80_, lean_object* v___x_81_, lean_object* v_snd_82_, lean_object* v_toNatCast_83_, lean_object* v_toMul_84_, lean_object* v___x_85_, lean_object* v_toSub_86_, lean_object* v_fst_87_, lean_object* v_i_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_89_ = lean_nat_mod(v___x_80_, v___x_81_);
v___x_90_ = lean_apply_1(v_snd_82_, v___x_89_);
lean_inc(v_i_88_);
v___x_91_ = lean_apply_1(v_toNatCast_83_, v_i_88_);
lean_inc(v_toMul_84_);
v___x_92_ = lean_apply_2(v_toMul_84_, v___x_91_, v___x_85_);
v___x_93_ = lean_apply_2(v_toSub_86_, v___x_90_, v___x_92_);
v___x_94_ = lean_apply_1(v_fst_87_, v_i_88_);
v___x_95_ = lean_apply_2(v_toMul_84_, v___x_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__1___boxed(lean_object* v___x_96_, lean_object* v___x_97_, lean_object* v_snd_98_, lean_object* v_toNatCast_99_, lean_object* v_toMul_100_, lean_object* v___x_101_, lean_object* v_toSub_102_, lean_object* v_fst_103_, lean_object* v_i_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__1(v___x_96_, v___x_97_, v_snd_98_, v_toNatCast_99_, v_toMul_100_, v___x_101_, v_toSub_102_, v_fst_103_, v_i_104_);
lean_dec(v___x_97_);
lean_dec(v___x_96_);
return v_res_105_;
}
}
static lean_object* _init_lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_mod(v___x_107_, v___x_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2(lean_object* v_d_109_, lean_object* v___x_110_, lean_object* v_A_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_commRing_113_; lean_object* v_toSemiring_114_; lean_object* v___x_115_; lean_object* v_toMul_116_; lean_object* v_toAddCommMonoid_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_toAddMonoidWithOne_120_; lean_object* v_toSub_121_; lean_object* v_toNatCast_122_; lean_object* v_fst_123_; lean_object* v_snd_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_commRing_113_ = lean_ctor_get(v_A_111_, 0);
lean_inc_ref(v_commRing_113_);
lean_dec_ref(v_A_111_);
v_toSemiring_114_ = lean_ctor_get(v_commRing_113_, 0);
lean_inc_ref(v_toSemiring_114_);
v___x_115_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_114_);
v_toMul_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_n(v_toMul_116_, 2);
lean_dec_ref(v___x_115_);
v_toAddCommMonoid_117_ = lean_ctor_get(v_toSemiring_114_, 0);
lean_inc_ref(v_toAddCommMonoid_117_);
v___x_118_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_commRing_113_);
v___x_119_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_118_);
v_toAddMonoidWithOne_120_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_toAddMonoidWithOne_120_);
lean_dec_ref(v___x_118_);
v_toSub_121_ = lean_ctor_get(v___x_119_, 2);
lean_inc(v_toSub_121_);
lean_dec_ref(v___x_119_);
v_toNatCast_122_ = lean_ctor_get(v_toAddMonoidWithOne_120_, 0);
lean_inc(v_toNatCast_122_);
lean_dec_ref(v_toAddMonoidWithOne_120_);
v_fst_123_ = lean_ctor_get(v___y_112_, 0);
lean_inc_n(v_fst_123_, 2);
v_snd_124_ = lean_ctor_get(v___y_112_, 1);
lean_inc_n(v_snd_124_, 2);
lean_dec_ref(v___y_112_);
v___f_125_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_125_, 0, v_fst_123_);
v___x_126_ = lean_nat_add(v_d_109_, v___x_110_);
v___x_127_ = lean_unsigned_to_nat(2u);
v___x_128_ = lean_obj_once(&lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___closed__0, &lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___closed__0_once, _init_lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___closed__0);
v___x_129_ = lean_apply_1(v_snd_124_, v___x_128_);
lean_inc(v___x_129_);
v___f_130_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_130_, 0, v___x_110_);
lean_closure_set(v___f_130_, 1, v___x_127_);
lean_closure_set(v___f_130_, 2, v_snd_124_);
lean_closure_set(v___f_130_, 3, v_toNatCast_122_);
lean_closure_set(v___f_130_, 4, v_toMul_116_);
lean_closure_set(v___f_130_, 5, v___x_129_);
lean_closure_set(v___f_130_, 6, v_toSub_121_);
lean_closure_set(v___f_130_, 7, v_fst_123_);
lean_inc(v___x_126_);
v___x_131_ = l_List_finRange(v___x_126_);
v___x_132_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_117_, v___x_131_, v___f_125_);
lean_dec_ref(v_toAddCommMonoid_117_);
v___x_133_ = lean_apply_2(v_toMul_116_, v___x_129_, v___x_132_);
v___x_134_ = lean_alloc_closure((void*)(lp_mathlib_Fin_cons___boxed), 5, 4);
lean_closure_set(v___x_134_, 0, v___x_126_);
lean_closure_set(v___x_134_, 1, lean_box(0));
lean_closure_set(v___x_134_, 2, v___x_133_);
lean_closure_set(v___x_134_, 3, v___f_130_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___boxed(lean_object* v_d_135_, lean_object* v___x_136_, lean_object* v_A_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2(v_d_135_, v___x_136_, v_A_137_, v___y_138_);
lean_dec(v_d_135_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___redArg(lean_object* v_d_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___f_142_; 
v___x_141_ = lean_unsigned_to_nat(1u);
v___f_142_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_projSpace_lineProductMap___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_142_, 0, v_d_140_);
lean_closure_set(v___f_142_, 1, v___x_141_);
return v___f_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap(lean_object* v_k_143_, lean_object* v_inst_144_, lean_object* v_d_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lp_GRH_New_Variety_projSpace_lineProductMap___redArg(v_d_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_projSpace_lineProductMap___boxed(lean_object* v_k_148_, lean_object* v_inst_149_, lean_object* v_d_150_, lean_object* v_inst_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_GRH_New_Variety_projSpace_lineProductMap(v_k_148_, v_inst_149_, v_d_150_, v_inst_151_);
lean_dec_ref(v_inst_149_);
return v_res_152_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_PointClass_NoetherNormalization(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_Primitive_PeriodCoefficients(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_PointClass_ProjectiveSpace(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_PointClass_NoetherNormalization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_Primitive_PeriodCoefficients(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
