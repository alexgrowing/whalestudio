// Lean compiler output
// Module: New.Derivatives.Divisibility.Count
// Imports: public import Init public meta import Init public import New.Derivatives.Divisibility.NullFrames public import New.Derivatives.FormalGroup.ThetaProducts
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_heightOneColumns___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_heightOneColumns___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_heightOneColumns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_lowColumnCount___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_lowColumnCount___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_lowColumnCount(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_lowBoxCount___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_lowBoxCount___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_lowBoxCount(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_eraseHeightOne___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_eraseHeightOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__0(lean_object* v_i_x27_1_, lean_object* v_00_u03c4_2_, lean_object* v_h_3_, lean_object* v_j_4_, lean_object* v_w_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc(v_h_3_);
lean_inc(v_00_u03c4_2_);
v___x_7_ = lean_apply_4(v_i_x27_1_, v_00_u03c4_2_, v_h_3_, v_j_4_, v_b_6_);
v___x_8_ = lean_apply_3(v_w_5_, v_00_u03c4_2_, v_h_3_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__1(lean_object* v_i_x27_9_, lean_object* v_00_u03c4_10_, lean_object* v_h_11_, lean_object* v_w_12_, lean_object* v___x_13_, lean_object* v_j_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_inc(v_h_11_);
v___f_15_ = lean_alloc_closure((void*)(lp_GRH_New_fillingCharge___redArg___lam__0), 6, 5);
lean_closure_set(v___f_15_, 0, v_i_x27_9_);
lean_closure_set(v___f_15_, 1, v_00_u03c4_10_);
lean_closure_set(v___f_15_, 2, v_h_11_);
lean_closure_set(v___f_15_, 3, v_j_14_);
lean_closure_set(v___f_15_, 4, v_w_12_);
v___x_16_ = l_List_finRange(v_h_11_);
v___x_17_ = lp_mathlib_Finset_sum___redArg(v___x_13_, v___x_16_, v___f_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__1___boxed(lean_object* v_i_x27_18_, lean_object* v_00_u03c4_19_, lean_object* v_h_20_, lean_object* v_w_21_, lean_object* v___x_22_, lean_object* v_j_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_fillingCharge___redArg___lam__1(v_i_x27_18_, v_00_u03c4_19_, v_h_20_, v_w_21_, v___x_22_, v_j_23_);
lean_dec_ref(v___x_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__2(lean_object* v_i_x27_25_, lean_object* v_00_u03c4_26_, lean_object* v_w_27_, lean_object* v___x_28_, lean_object* v_00_u03ba_29_, lean_object* v_h_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc_ref(v___x_28_);
lean_inc(v_h_30_);
lean_inc(v_00_u03c4_26_);
v___f_31_ = lean_alloc_closure((void*)(lp_GRH_New_fillingCharge___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_31_, 0, v_i_x27_25_);
lean_closure_set(v___f_31_, 1, v_00_u03c4_26_);
lean_closure_set(v___f_31_, 2, v_h_30_);
lean_closure_set(v___f_31_, 3, v_w_27_);
lean_closure_set(v___f_31_, 4, v___x_28_);
v___x_32_ = lean_apply_2(v_00_u03ba_29_, v_00_u03c4_26_, v_h_30_);
v___x_33_ = l_List_finRange(v___x_32_);
v___x_34_ = lp_mathlib_Finset_sum___redArg(v___x_28_, v___x_33_, v___f_31_);
lean_dec_ref(v___x_28_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__3(lean_object* v_i_x27_35_, lean_object* v_w_36_, lean_object* v___x_37_, lean_object* v_00_u03ba_38_, lean_object* v_inst_39_, lean_object* v_00_u03c4_40_){
_start:
{
lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc_ref(v___x_37_);
v___f_41_ = lean_alloc_closure((void*)(lp_GRH_New_fillingCharge___redArg___lam__2), 6, 5);
lean_closure_set(v___f_41_, 0, v_i_x27_35_);
lean_closure_set(v___f_41_, 1, v_00_u03c4_40_);
lean_closure_set(v___f_41_, 2, v_w_36_);
lean_closure_set(v___f_41_, 3, v___x_37_);
lean_closure_set(v___f_41_, 4, v_00_u03ba_38_);
v___x_42_ = l_List_lengthTR___redArg(v_inst_39_);
v___x_43_ = l_List_finRange(v___x_42_);
v___x_44_ = lp_mathlib_Finset_sum___redArg(v___x_37_, v___x_43_, v___f_41_);
lean_dec_ref(v___x_37_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg___lam__3___boxed(lean_object* v_i_x27_45_, lean_object* v_w_46_, lean_object* v___x_47_, lean_object* v_00_u03ba_48_, lean_object* v_inst_49_, lean_object* v_00_u03c4_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_GRH_New_fillingCharge___redArg___lam__3(v_i_x27_45_, v_w_46_, v___x_47_, v_00_u03ba_48_, v_inst_49_, v_00_u03c4_50_);
lean_dec(v_inst_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_00_u03ba_54_, lean_object* v_w_55_, lean_object* v_i_x27_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___x_59_; 
v___x_57_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___f_58_ = lean_alloc_closure((void*)(lp_GRH_New_fillingCharge___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_58_, 0, v_i_x27_56_);
lean_closure_set(v___f_58_, 1, v_w_55_);
lean_closure_set(v___f_58_, 2, v___x_57_);
lean_closure_set(v___f_58_, 3, v_00_u03ba_54_);
lean_closure_set(v___f_58_, 4, v_inst_53_);
v___x_59_ = lp_mathlib_Finset_sum___redArg(v___x_57_, v_inst_52_, v___f_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge(lean_object* v_00_u03a6_60_, lean_object* v_n_x27_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_00_u03ba_65_, lean_object* v_w_66_, lean_object* v_i_x27_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_GRH_New_fillingCharge___redArg(v_inst_62_, v_inst_63_, v_00_u03ba_65_, v_w_66_, v_i_x27_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_fillingCharge___boxed(lean_object* v_00_u03a6_69_, lean_object* v_n_x27_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_00_u03ba_74_, lean_object* v_w_75_, lean_object* v_i_x27_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_GRH_New_fillingCharge(v_00_u03a6_69_, v_n_x27_70_, v_inst_71_, v_inst_72_, v_inst_73_, v_00_u03ba_74_, v_w_75_, v_i_x27_76_);
lean_dec_ref(v_inst_73_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_heightOneColumns___redArg___lam__0(lean_object* v_00_u03ba_78_, lean_object* v_00_u03c4_79_, lean_object* v_h_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_dec_eq(v_h_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h_80_);
lean_dec(v_00_u03c4_79_);
lean_dec_ref(v_00_u03ba_78_);
v___x_83_ = lean_unsigned_to_nat(0u);
return v___x_83_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_2(v_00_u03ba_78_, v_00_u03c4_79_, v_h_80_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_heightOneColumns___redArg(lean_object* v_00_u03ba_85_, lean_object* v_N_86_, lean_object* v_00_u03c4_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___f_88_ = lean_alloc_closure((void*)(lp_GRH_New_heightOneColumns___redArg___lam__0), 3, 2);
lean_closure_set(v___f_88_, 0, v_00_u03ba_85_);
lean_closure_set(v___f_88_, 1, v_00_u03c4_87_);
v___x_89_ = l_List_range(v_N_86_);
v___x_90_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_89_, v___f_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_heightOneColumns(lean_object* v_00_u03a6_91_, lean_object* v_00_u03ba_92_, lean_object* v_N_93_, lean_object* v_00_u03c4_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lp_GRH_New_heightOneColumns___redArg(v_00_u03ba_92_, v_N_93_, v_00_u03c4_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_lowColumnCount___redArg___lam__0(lean_object* v_00_u03ba_96_, lean_object* v_00_u03c4_97_, lean_object* v_h_98_){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_dec_eq(v_h_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_apply_2(v_00_u03ba_96_, v_00_u03c4_97_, v_h_98_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
lean_dec(v_h_98_);
lean_dec(v_00_u03c4_97_);
lean_dec_ref(v_00_u03ba_96_);
v___x_102_ = lean_unsigned_to_nat(0u);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_lowColumnCount___redArg(lean_object* v_00_u03ba_103_, lean_object* v_N_104_, lean_object* v_00_u03c4_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___f_106_ = lean_alloc_closure((void*)(lp_GRH_New_lowColumnCount___redArg___lam__0), 3, 2);
lean_closure_set(v___f_106_, 0, v_00_u03ba_103_);
lean_closure_set(v___f_106_, 1, v_00_u03c4_105_);
v___x_107_ = l_List_range(v_N_104_);
v___x_108_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_107_, v___f_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_lowColumnCount(lean_object* v_00_u03a6_109_, lean_object* v_00_u03ba_110_, lean_object* v_N_111_, lean_object* v_00_u03c4_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lp_GRH_New_lowColumnCount___redArg(v_00_u03ba_110_, v_N_111_, v_00_u03c4_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_lowBoxCount___redArg___lam__0(lean_object* v_00_u03ba_114_, lean_object* v_00_u03c4_115_, lean_object* v_h_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_dec_eq(v_h_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_inc(v_h_116_);
v___x_119_ = lean_apply_2(v_00_u03ba_114_, v_00_u03c4_115_, v_h_116_);
v___x_120_ = lean_nat_mul(v_h_116_, v___x_119_);
lean_dec(v___x_119_);
lean_dec(v_h_116_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h_116_);
lean_dec(v_00_u03c4_115_);
lean_dec_ref(v_00_u03ba_114_);
v___x_121_ = lean_unsigned_to_nat(0u);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_lowBoxCount___redArg(lean_object* v_00_u03ba_122_, lean_object* v_N_123_, lean_object* v_00_u03c4_124_){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___f_125_ = lean_alloc_closure((void*)(lp_GRH_New_lowBoxCount___redArg___lam__0), 3, 2);
lean_closure_set(v___f_125_, 0, v_00_u03ba_122_);
lean_closure_set(v___f_125_, 1, v_00_u03c4_124_);
v___x_126_ = l_List_range(v_N_123_);
v___x_127_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_126_, v___f_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_lowBoxCount(lean_object* v_00_u03a6_128_, lean_object* v_00_u03ba_129_, lean_object* v_N_130_, lean_object* v_00_u03c4_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_GRH_New_lowBoxCount___redArg(v_00_u03ba_129_, v_N_130_, v_00_u03c4_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_eraseHeightOne___redArg(lean_object* v_inst_133_, lean_object* v_00_u03ba_134_, lean_object* v_ev_135_, lean_object* v_00_u03c4_136_, lean_object* v_h_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_dec_eq(v_h_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec(v_ev_135_);
lean_dec_ref(v_inst_133_);
v___x_140_ = lean_apply_2(v_00_u03ba_134_, v_00_u03c4_136_, v_h_137_);
return v___x_140_;
}
else
{
lean_object* v___f_141_; uint8_t v___x_142_; 
v___f_141_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_141_, 0, v_inst_133_);
lean_inc(v_00_u03c4_136_);
v___x_142_ = l_List_elem___redArg(v___f_141_, v_00_u03c4_136_, v_ev_135_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_2(v_00_u03ba_134_, v_00_u03c4_136_, v_h_137_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
lean_dec(v_h_137_);
lean_dec(v_00_u03c4_136_);
lean_dec_ref(v_00_u03ba_134_);
v___x_144_ = lean_unsigned_to_nat(0u);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_eraseHeightOne(lean_object* v_00_u03a6_145_, lean_object* v_inst_146_, lean_object* v_00_u03ba_147_, lean_object* v_ev_148_, lean_object* v_00_u03c4_149_, lean_object* v_h_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lp_GRH_New_eraseHeightOne___redArg(v_inst_146_, v_00_u03ba_147_, v_ev_148_, v_00_u03c4_149_, v_h_150_);
return v___x_151_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Divisibility_NullFrames(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_FormalGroup_ThetaProducts(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_Divisibility_Count(uint8_t builtin) {
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
res = initialize_GRH_New_Derivatives_Divisibility_NullFrames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Derivatives_FormalGroup_ThetaProducts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
