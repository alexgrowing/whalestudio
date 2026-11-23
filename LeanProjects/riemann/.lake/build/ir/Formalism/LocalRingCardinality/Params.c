// Lean compiler output
// Module: Formalism.LocalRingCardinality.Params
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_n(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_n___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_f___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_r___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_N___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rS(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rS___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankY(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankY___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankX_x27(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankX_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigY0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigY0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_sExp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_sExp___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp_x27___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_wG___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_wG___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_wG(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_n(lean_object* v_R_1_){
_start:
{
lean_object* v_toFrame_2_; lean_object* v_ord_3_; 
v_toFrame_2_ = lean_ctor_get(v_R_1_, 0);
v_ord_3_ = lean_ctor_get(v_toFrame_2_, 1);
lean_inc(v_ord_3_);
return v_ord_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_n___boxed(lean_object* v_R_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_BasicNotions_Ranks_n(v_R_4_);
lean_dec_ref(v_R_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object* v_R_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lp_tree_Formalism_BasicNotions_Ranks_n(v_R_6_);
v___x_9_ = lean_nat_mul(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_f___boxed(lean_object* v_R_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_10_);
lean_dec_ref(v_R_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object* v_R_12_){
_start:
{
lean_object* v_k_13_; lean_object* v_m_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_k_13_ = lean_ctor_get(v_R_12_, 1);
v_m_14_ = lean_ctor_get(v_R_12_, 2);
v___x_15_ = lean_nat_add(v_k_13_, v_m_14_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_sub(v___x_15_, v___x_16_);
lean_dec(v___x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_r___boxed(lean_object* v_R_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_18_);
lean_dec_ref(v_R_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object* v_R_20_){
_start:
{
lean_object* v_t_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_t_21_ = lean_ctor_get(v_R_20_, 3);
v___x_22_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_20_);
v___x_23_ = lean_nat_add(v___x_22_, v_t_21_);
lean_dec(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV___boxed(lean_object* v_R_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_24_);
lean_dec_ref(v_R_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object* v_R_26_, lean_object* v_j_27_){
_start:
{
lean_object* v_k_28_; lean_object* v_t_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_k_28_ = lean_ctor_get(v_R_26_, 1);
v_t_29_ = lean_ctor_get(v_R_26_, 3);
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = lean_nat_add(v_t_29_, v___x_30_);
v___x_32_ = lean_nat_mul(v_j_27_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_nat_add(v_k_28_, v___x_32_);
lean_dec(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_N___boxed(lean_object* v_R_34_, lean_object* v_j_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_34_, v_j_35_);
lean_dec(v_j_35_);
lean_dec_ref(v_R_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rS(lean_object* v_R_37_){
_start:
{
lean_object* v_m_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_m_38_ = lean_ctor_get(v_R_37_, 2);
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_shiftr(v_m_38_, v___x_39_);
v___x_41_ = lean_nat_sub(v___x_40_, v___x_39_);
lean_dec(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rS___boxed(lean_object* v_R_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_BasicNotions_Ranks_rS(v_R_42_);
lean_dec_ref(v_R_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankY(lean_object* v_R_44_, lean_object* v_j_45_){
_start:
{
lean_object* v_t_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_t_46_ = lean_ctor_get(v_R_44_, 3);
v___x_47_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_44_);
v___x_48_ = lean_nat_mul(v_j_45_, v_t_46_);
v___x_49_ = lean_nat_add(v___x_47_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankY___boxed(lean_object* v_R_50_, lean_object* v_j_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_tree_Formalism_BasicNotions_Ranks_rankY(v_R_50_, v_j_51_);
lean_dec(v_j_51_);
lean_dec_ref(v_R_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankX_x27(lean_object* v_R_53_){
_start:
{
lean_object* v_m_54_; lean_object* v_t_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_m_54_ = lean_ctor_get(v_R_53_, 2);
v_t_55_ = lean_ctor_get(v_R_53_, 3);
v___x_56_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_53_);
v___x_57_ = lean_nat_mul(v_m_54_, v_t_55_);
v___x_58_ = lean_nat_add(v___x_56_, v___x_57_);
lean_dec(v___x_57_);
lean_dec(v___x_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankX_x27___boxed(lean_object* v_R_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_BasicNotions_Ranks_rankX_x27(v_R_59_);
lean_dec_ref(v_R_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigY0(lean_object* v_R_61_){
_start:
{
lean_object* v_k_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_k_62_ = lean_ctor_get(v_R_61_, 1);
v___x_63_ = lp_tree_Formalism_BasicNotions_Ranks_rS(v_R_61_);
v___x_64_ = lean_nat_add(v_k_62_, v___x_63_);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v___x_63_, v___x_65_);
lean_dec(v___x_63_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigY0___boxed(lean_object* v_R_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Formalism_BasicNotions_Ranks_sigY0(v_R_68_);
lean_dec_ref(v_R_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object* v_R_70_, lean_object* v_j_71_){
_start:
{
lean_object* v_k_72_; lean_object* v_m_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_k_72_ = lean_ctor_get(v_R_70_, 1);
v_m_73_ = lean_ctor_get(v_R_70_, 2);
v___x_74_ = lean_nat_add(v_k_72_, v_j_71_);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_sub(v___x_74_, v___x_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_nat_sub(v_m_73_, v_j_71_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW___boxed(lean_object* v_R_79_, lean_object* v_j_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_79_, v_j_80_);
lean_dec(v_j_80_);
lean_dec_ref(v_R_79_);
return v_res_81_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_sExp___closed__0(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp(lean_object* v_R_84_, lean_object* v_ej_85_, lean_object* v_j_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_sub(v_j_86_, v___x_87_);
v___x_89_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_84_, v___x_88_);
lean_dec(v___x_88_);
v___x_90_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_89_);
v___x_91_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_sExp___closed__0, &lp_tree_Formalism_BasicNotions_sExp___closed__0_once, _init_lp_tree_Formalism_BasicNotions_sExp___closed__0);
v___x_92_ = l_Rat_div(v___x_90_, v___x_91_);
lean_dec_ref(v___x_90_);
v___x_93_ = l_Rat_sub(v_ej_85_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp___boxed(lean_object* v_R_94_, lean_object* v_ej_95_, lean_object* v_j_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_Formalism_BasicNotions_sExp(v_R_94_, v_ej_95_, v_j_96_);
lean_dec(v_j_96_);
lean_dec_ref(v_R_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp_x27(lean_object* v_R_98_, lean_object* v_ej_99_, lean_object* v_j_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_101_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_98_, v_j_100_);
v___x_102_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_101_);
v___x_103_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_sExp___closed__0, &lp_tree_Formalism_BasicNotions_sExp___closed__0_once, _init_lp_tree_Formalism_BasicNotions_sExp___closed__0);
v___x_104_ = l_Rat_div(v___x_102_, v___x_103_);
lean_dec_ref(v___x_102_);
v___x_105_ = l_Rat_sub(v_ej_99_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sExp_x27___boxed(lean_object* v_R_106_, lean_object* v_ej_107_, lean_object* v_j_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Formalism_BasicNotions_sExp_x27(v_R_106_, v_ej_107_, v_j_108_);
lean_dec(v_j_108_);
lean_dec_ref(v_R_106_);
return v_res_109_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_wG___closed__0(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_wG(lean_object* v_R_112_, lean_object* v_ej_113_, lean_object* v_j_114_){
_start:
{
lean_object* v_k_115_; lean_object* v_t_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_k_115_ = lean_ctor_get(v_R_112_, 1);
lean_inc(v_k_115_);
v_t_116_ = lean_ctor_get(v_R_112_, 3);
lean_inc(v_t_116_);
lean_dec_ref(v_R_112_);
v___x_117_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_k_115_);
v___x_118_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_sExp___closed__0, &lp_tree_Formalism_BasicNotions_sExp___closed__0_once, _init_lp_tree_Formalism_BasicNotions_sExp___closed__0);
v___x_119_ = l_Rat_div(v___x_117_, v___x_118_);
lean_dec_ref(v___x_117_);
v___x_120_ = l_Rat_sub(v_ej_113_, v___x_119_);
v___x_121_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_j_114_);
v___x_122_ = l_Rat_mul(v___x_118_, v___x_121_);
v___x_123_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_wG___closed__0, &lp_tree_Formalism_BasicNotions_wG___closed__0_once, _init_lp_tree_Formalism_BasicNotions_wG___closed__0);
v___x_124_ = l_Rat_sub(v___x_122_, v___x_123_);
v___x_125_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_116_);
v___x_126_ = l_Rat_add(v___x_125_, v___x_123_);
v___x_127_ = l_Rat_mul(v___x_124_, v___x_126_);
lean_dec_ref(v___x_124_);
v___x_128_ = l_Rat_div(v___x_127_, v___x_118_);
lean_dec_ref(v___x_127_);
v___x_129_ = l_Rat_sub(v___x_120_, v___x_128_);
return v___x_129_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EvalFrameOrd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EvalFrameOrd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
