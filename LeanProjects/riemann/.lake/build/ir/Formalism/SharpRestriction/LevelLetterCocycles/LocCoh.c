// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.WeaklyAdmissibleFiltrations.Statement public import Formalism.WeaklyAdmissibleFiltrations.StatementTor public import ReciprocityTheory.BasicDefinitions.AdRep
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
lean_object* lp_mathlib_NonUnitalRingHom_instFunLike___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_restrictScalars___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_mapQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cycLL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cycLL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cycLL___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cupL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cupL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cupL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cycLL___redArg(lean_object* v_PD_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v_algebraMap_3_; lean_object* v_00_u03c7_4_; lean_object* v___x_5_; lean_object* v___f_6_; lean_object* v___f_7_; 
v_algebraMap_3_ = lean_ctor_get(v_inst_2_, 1);
lean_inc(v_algebraMap_3_);
lean_dec_ref(v_inst_2_);
v_00_u03c7_4_ = lean_ctor_get(v_PD_1_, 7);
lean_inc_ref(v_00_u03c7_4_);
lean_dec_ref(v_PD_1_);
v___x_5_ = lean_alloc_closure((void*)(lp_mathlib_NonUnitalRingHom_instFunLike___lam__0), 2, 1);
lean_closure_set(v___x_5_, 0, v_algebraMap_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_7_, 0, v_00_u03c7_4_);
lean_closure_set(v___f_7_, 1, v___f_6_);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cycLL(lean_object* v_G_8_, lean_object* v_inst_9_, lean_object* v_Qp_10_, lean_object* v_K_u2080_11_, lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_B_20_, lean_object* v_BdR_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_PD_33_, lean_object* v_LL_34_, lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_Formalism_MainNotions_N_cycLL___redArg(v_PD_33_, v_inst_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cycLL___boxed(lean_object** _args){
lean_object* v_G_38_ = _args[0];
lean_object* v_inst_39_ = _args[1];
lean_object* v_Qp_40_ = _args[2];
lean_object* v_K_u2080_41_ = _args[3];
lean_object* v_K_42_ = _args[4];
lean_object* v_inst_43_ = _args[5];
lean_object* v_inst_44_ = _args[6];
lean_object* v_inst_45_ = _args[7];
lean_object* v_inst_46_ = _args[8];
lean_object* v_inst_47_ = _args[9];
lean_object* v_inst_48_ = _args[10];
lean_object* v_inst_49_ = _args[11];
lean_object* v_B_50_ = _args[12];
lean_object* v_BdR_51_ = _args[13];
lean_object* v_inst_52_ = _args[14];
lean_object* v_inst_53_ = _args[15];
lean_object* v_inst_54_ = _args[16];
lean_object* v_inst_55_ = _args[17];
lean_object* v_inst_56_ = _args[18];
lean_object* v_inst_57_ = _args[19];
lean_object* v_inst_58_ = _args[20];
lean_object* v_inst_59_ = _args[21];
lean_object* v_inst_60_ = _args[22];
lean_object* v_inst_61_ = _args[23];
lean_object* v_inst_62_ = _args[24];
lean_object* v_PD_63_ = _args[25];
lean_object* v_LL_64_ = _args[26];
lean_object* v_inst_65_ = _args[27];
lean_object* v_inst_66_ = _args[28];
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_Formalism_MainNotions_N_cycLL(v_G_38_, v_inst_39_, v_Qp_40_, v_K_u2080_41_, v_K_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_inst_49_, v_B_50_, v_BdR_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_inst_62_, v_PD_63_, v_LL_64_, v_inst_65_, v_inst_66_);
lean_dec_ref(v_inst_65_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_58_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_54_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
lean_dec_ref(v_inst_45_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_39_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD___redArg___lam__0(lean_object* v_00_u03c1_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_L_72_, lean_object* v_g_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v___x_87__overap_77_; lean_object* v___x_78_; 
v___x_75_ = lean_apply_1(v_00_u03c1_68_, v_g_73_);
v___f_76_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_restrictScalars___redArg___lam__0), 2, 1);
lean_closure_set(v___f_76_, 0, v___x_75_);
v___x_87__overap_77_ = lp_mathlib_Submodule_mapQ___redArg(v_inst_69_, v_inst_70_, v_inst_71_, v_L_72_, v___f_76_);
v___x_78_ = lean_apply_1(v___x_87__overap_77_, v___y_74_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD___redArg(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_00_u03c1_82_, lean_object* v_L_83_){
_start:
{
lean_object* v___f_84_; 
v___f_84_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_repD___redArg___lam__0), 7, 5);
lean_closure_set(v___f_84_, 0, v_00_u03c1_82_);
lean_closure_set(v___f_84_, 1, v_inst_79_);
lean_closure_set(v___f_84_, 2, v_inst_80_);
lean_closure_set(v___f_84_, 3, v_inst_81_);
lean_closure_set(v___f_84_, 4, v_L_83_);
return v___f_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD(lean_object* v_G_85_, lean_object* v_inst_86_, lean_object* v_LL_87_, lean_object* v_inst_88_, lean_object* v_O_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_V_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_00_u03c1_97_, lean_object* v_L_98_){
_start:
{
lean_object* v___f_99_; 
v___f_99_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_repD___redArg___lam__0), 7, 5);
lean_closure_set(v___f_99_, 0, v_00_u03c1_97_);
lean_closure_set(v___f_99_, 1, v_inst_90_);
lean_closure_set(v___f_99_, 2, v_inst_93_);
lean_closure_set(v___f_99_, 3, v_inst_95_);
lean_closure_set(v___f_99_, 4, v_L_98_);
return v___f_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repD___boxed(lean_object* v_G_100_, lean_object* v_inst_101_, lean_object* v_LL_102_, lean_object* v_inst_103_, lean_object* v_O_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_V_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_00_u03c1_112_, lean_object* v_L_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_tree_Formalism_MainNotions_N_repD(v_G_100_, v_inst_101_, v_LL_102_, v_inst_103_, v_O_104_, v_inst_105_, v_inst_106_, v_V_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_00_u03c1_112_, v_L_113_);
lean_dec(v_inst_109_);
lean_dec_ref(v_inst_106_);
lean_dec_ref(v_inst_103_);
lean_dec_ref(v_inst_101_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cupL___redArg(lean_object* v_00_u03c1_x27_115_, lean_object* v_P_116_, lean_object* v_a_117_, lean_object* v_b_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_fst_120_ = lean_ctor_get(v_x_119_, 0);
lean_inc_n(v_fst_120_, 2);
v_snd_121_ = lean_ctor_get(v_x_119_, 1);
lean_inc(v_snd_121_);
lean_dec_ref(v_x_119_);
v___x_122_ = lean_apply_1(v_a_117_, v_fst_120_);
v___x_123_ = lean_apply_1(v_b_118_, v_snd_121_);
v___x_124_ = lean_apply_2(v_00_u03c1_x27_115_, v_fst_120_, v___x_123_);
v___x_125_ = lean_apply_2(v_P_116_, v___x_122_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cupL(lean_object* v_G_126_, lean_object* v_inst_127_, lean_object* v_LL_128_, lean_object* v_inst_129_, lean_object* v_V_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_V_x27_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_00_u03c1_x27_136_, lean_object* v_P_137_, lean_object* v_a_138_, lean_object* v_b_139_, lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lp_tree_Formalism_MainNotions_N_cupL___redArg(v_00_u03c1_x27_136_, v_P_137_, v_a_138_, v_b_139_, v_x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_cupL___boxed(lean_object* v_G_142_, lean_object* v_inst_143_, lean_object* v_LL_144_, lean_object* v_inst_145_, lean_object* v_V_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_V_x27_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_00_u03c1_x27_152_, lean_object* v_P_153_, lean_object* v_a_154_, lean_object* v_b_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_tree_Formalism_MainNotions_N_cupL(v_G_142_, v_inst_143_, v_LL_144_, v_inst_145_, v_V_146_, v_inst_147_, v_inst_148_, v_V_x27_149_, v_inst_150_, v_inst_151_, v_00_u03c1_x27_152_, v_P_153_, v_a_154_, v_b_155_, v_x_156_);
lean_dec(v_inst_151_);
lean_dec_ref(v_inst_150_);
lean_dec(v_inst_148_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_145_);
lean_dec_ref(v_inst_143_);
return v_res_157_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_WeaklyAdmissibleFiltrations_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_WeaklyAdmissibleFiltrations_StatementTor(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_BasicDefinitions_AdRep(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh(uint8_t builtin) {
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
res = initialize_tree_Formalism_WeaklyAdmissibleFiltrations_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_WeaklyAdmissibleFiltrations_StatementTor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_BasicDefinitions_AdRep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
