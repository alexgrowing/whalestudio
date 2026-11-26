// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.Edges
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.HermiteForm public import Lib.LocalGL.Green.HallAlgebra public import New.UpperBound.ElementaryDivisors.InvariantAverage public import New.UpperBound.ElementaryDivisors.RootLemma
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
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instCommMonoid;
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___lam__0(lean_object* v_00_u03b2_1_, lean_object* v_s_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toFun_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_apply_1(v_00_u03b2_1_, v_s_2_);
v_toFun_5_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_toFun_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_apply_1(v_toFun_5_, v_b_3_);
v___x_7_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_6_);
lean_dec(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___lam__1(lean_object* v_00_u03b2_8_, lean_object* v_k_9_, lean_object* v___x_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_12_ = lean_alloc_closure((void*)(lp_GRH_New_dividedPowerCoeff___redArg___lam__0), 3, 2);
lean_closure_set(v___f_12_, 0, v_00_u03b2_8_);
lean_closure_set(v___f_12_, 1, v_s_11_);
v___x_13_ = l_List_finRange(v_k_9_);
v___x_14_ = lp_mathlib_Finset_prod___redArg(v___x_10_, v___x_13_, v___f_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___lam__1___boxed(lean_object* v_00_u03b2_15_, lean_object* v_k_16_, lean_object* v___x_17_, lean_object* v_s_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_GRH_New_dividedPowerCoeff___redArg___lam__1(v_00_u03b2_15_, v_k_16_, v___x_17_, v_s_18_);
lean_dec_ref(v___x_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg(lean_object* v_N_20_, lean_object* v_k_21_, lean_object* v_n_22_, lean_object* v_00_u03b2_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = lp_mathlib_Nat_instCommMonoid;
v___f_25_ = lean_alloc_closure((void*)(lp_GRH_New_dividedPowerCoeff___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_25_, 0, v_00_u03b2_23_);
lean_closure_set(v___f_25_, 1, v_k_21_);
lean_closure_set(v___f_25_, 2, v___x_24_);
v___x_26_ = lp_mathlib_Nat_factorialBinarySplitting(v_n_22_);
v___x_27_ = lean_nat_pow(v___x_26_, v_N_20_);
lean_dec(v___x_26_);
v___x_28_ = lp_mathlib_ZMod_fintype___redArg(v_N_20_);
v___x_29_ = lp_mathlib_Finset_prod___redArg(v___x_24_, v___x_28_, v___f_25_);
v___x_30_ = lean_nat_div(v___x_27_, v___x_29_);
lean_dec(v___x_29_);
lean_dec(v___x_27_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___redArg___boxed(lean_object* v_N_31_, lean_object* v_k_32_, lean_object* v_n_33_, lean_object* v_00_u03b2_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_GRH_New_dividedPowerCoeff___redArg(v_N_31_, v_k_32_, v_n_33_, v_00_u03b2_34_);
lean_dec(v_n_33_);
lean_dec(v_N_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff(lean_object* v_N_36_, lean_object* v_k_37_, lean_object* v_n_38_, lean_object* v_inst_39_, lean_object* v_00_u03b2_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_GRH_New_dividedPowerCoeff___redArg(v_N_36_, v_k_37_, v_n_38_, v_00_u03b2_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dividedPowerCoeff___boxed(lean_object* v_N_42_, lean_object* v_k_43_, lean_object* v_n_44_, lean_object* v_inst_45_, lean_object* v_00_u03b2_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_GRH_New_dividedPowerCoeff(v_N_42_, v_k_43_, v_n_44_, v_inst_45_, v_00_u03b2_46_);
lean_dec(v_n_44_);
lean_dec(v_N_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms___redArg(){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms___redArg___boxed(lean_object* v___dummy_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_GRH_New_FrobeniusCycle_allEdgesForms___redArg();
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms(lean_object* v_N_52_, lean_object* v_W_53_, lean_object* v_O_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_T_59_, lean_object* v_k_60_, lean_object* v_n_61_, lean_object* v_r_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_allEdgesForms___boxed(lean_object* v_N_64_, lean_object* v_W_65_, lean_object* v_O_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_T_71_, lean_object* v_k_72_, lean_object* v_n_73_, lean_object* v_r_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_GRH_New_FrobeniusCycle_allEdgesForms(v_N_64_, v_W_65_, v_O_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_inst_70_, v_T_71_, v_k_72_, v_n_73_, v_r_74_);
lean_dec(v_r_74_);
lean_dec(v_n_73_);
lean_dec(v_k_72_);
lean_dec_ref(v_T_71_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_68_);
lean_dec(v_N_64_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg(lean_object* v_N_76_, lean_object* v_T_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_frobExp_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_frobExp_79_ = lean_ctor_get(v_T_77_, 1);
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_pow(v_k_78_, v___x_80_);
v___x_82_ = lean_nat_mul(v_frobExp_79_, v_N_76_);
v___x_83_ = lean_nat_mul(v___x_81_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg___boxed(lean_object* v_N_84_, lean_object* v_T_85_, lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg(v_N_84_, v_T_85_, v_k_86_);
lean_dec(v_k_86_);
lean_dec_ref(v_T_85_);
lean_dec(v_N_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent(lean_object* v_N_88_, lean_object* v_W_89_, lean_object* v_O_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_T_94_, lean_object* v_k_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg(v_N_88_, v_T_94_, v_k_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___boxed(lean_object* v_N_97_, lean_object* v_W_98_, lean_object* v_O_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_T_103_, lean_object* v_k_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_GRH_New_FrobeniusCycle_multinomialExponent(v_N_97_, v_W_98_, v_O_99_, v_inst_100_, v_inst_101_, v_inst_102_, v_T_103_, v_k_104_);
lean_dec(v_k_104_);
lean_dec_ref(v_T_103_);
lean_dec_ref(v_inst_102_);
lean_dec_ref(v_inst_100_);
lean_dec(v_N_97_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions___redArg(){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(0);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions___redArg___boxed(lean_object* v___dummy_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_GRH_New_FrobeniusCycle_originFunctions___redArg();
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions(lean_object* v_N_110_, lean_object* v_k_111_, lean_object* v_W_112_, lean_object* v_O_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_T_118_, lean_object* v_X_119_, lean_object* v_E_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_n_123_, lean_object* v_r_124_, lean_object* v_src_125_, lean_object* v_g_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_originFunctions___boxed(lean_object** _args){
lean_object* v_N_128_ = _args[0];
lean_object* v_k_129_ = _args[1];
lean_object* v_W_130_ = _args[2];
lean_object* v_O_131_ = _args[3];
lean_object* v_inst_132_ = _args[4];
lean_object* v_inst_133_ = _args[5];
lean_object* v_inst_134_ = _args[6];
lean_object* v_inst_135_ = _args[7];
lean_object* v_T_136_ = _args[8];
lean_object* v_X_137_ = _args[9];
lean_object* v_E_138_ = _args[10];
lean_object* v_inst_139_ = _args[11];
lean_object* v_inst_140_ = _args[12];
lean_object* v_n_141_ = _args[13];
lean_object* v_r_142_ = _args[14];
lean_object* v_src_143_ = _args[15];
lean_object* v_g_144_ = _args[16];
_start:
{
lean_object* v_res_145_; 
v_res_145_ = lp_GRH_New_FrobeniusCycle_originFunctions(v_N_128_, v_k_129_, v_W_130_, v_O_131_, v_inst_132_, v_inst_133_, v_inst_134_, v_inst_135_, v_T_136_, v_X_137_, v_E_138_, v_inst_139_, v_inst_140_, v_n_141_, v_r_142_, v_src_143_, v_g_144_);
lean_dec_ref(v_g_144_);
lean_dec(v_src_143_);
lean_dec(v_r_142_);
lean_dec(v_n_141_);
lean_dec_ref(v_inst_140_);
lean_dec(v_inst_139_);
lean_dec_ref(v_T_136_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_133_);
lean_dec(v_k_129_);
lean_dec(v_N_128_);
return v_res_145_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_HermiteForm(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Green_HallAlgebra(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_InvariantAverage(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_Edges(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_HermiteForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_LocalGL_Green_HallAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_InvariantAverage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
