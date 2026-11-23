// Lean compiler output
// Module: ReciprocityTheory.BasicDefinitions.AdRep
// Imports: public import Init public meta import Init public import ReciprocityTheory.BasicDefinitions.ExistsUnique
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C1(lean_object* v_k_1_, lean_object* v_inst_2_, lean_object* v_M_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_G_6_, lean_object* v_inst_7_, lean_object* v_N_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C1___boxed(lean_object* v_k_10_, lean_object* v_inst_11_, lean_object* v_M_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_G_15_, lean_object* v_inst_16_, lean_object* v_N_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_ReciprocityTheory_Def_C1(v_k_10_, v_inst_11_, v_M_12_, v_inst_13_, v_inst_14_, v_G_15_, v_inst_16_, v_N_17_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C2(lean_object* v_k_19_, lean_object* v_inst_20_, lean_object* v_M_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_G_24_, lean_object* v_inst_25_, lean_object* v_N_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_C2___boxed(lean_object* v_k_28_, lean_object* v_inst_29_, lean_object* v_M_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_G_33_, lean_object* v_inst_34_, lean_object* v_N_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_ReciprocityTheory_Def_C2(v_k_28_, v_inst_29_, v_M_30_, v_inst_31_, v_inst_32_, v_G_33_, v_inst_34_, v_N_35_);
lean_dec(v_inst_32_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_29_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0___redArg___lam__0(lean_object* v_00_u03c0_37_, lean_object* v_toSub_38_, lean_object* v_m_39_, lean_object* v_g_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc(v_m_39_);
v___x_41_ = lean_apply_2(v_00_u03c0_37_, v_g_40_, v_m_39_);
v___x_42_ = lean_apply_2(v_toSub_38_, v___x_41_, v_m_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0___redArg(lean_object* v_inst_43_, lean_object* v_00_u03c0_44_){
_start:
{
lean_object* v_toSub_45_; lean_object* v___f_46_; 
v_toSub_45_ = lean_ctor_get(v_inst_43_, 2);
lean_inc(v_toSub_45_);
lean_dec_ref(v_inst_43_);
v___f_46_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_d0___redArg___lam__0), 4, 2);
lean_closure_set(v___f_46_, 0, v_00_u03c0_44_);
lean_closure_set(v___f_46_, 1, v_toSub_45_);
return v___f_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0(lean_object* v_k_47_, lean_object* v_inst_48_, lean_object* v_G_49_, lean_object* v_inst_50_, lean_object* v_M_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_00_u03c0_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_ReciprocityTheory_Def_d0___redArg(v_inst_52_, v_00_u03c0_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d0___boxed(lean_object* v_k_56_, lean_object* v_inst_57_, lean_object* v_G_58_, lean_object* v_inst_59_, lean_object* v_M_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_00_u03c0_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_ReciprocityTheory_Def_d0(v_k_56_, v_inst_57_, v_G_58_, v_inst_59_, v_M_60_, v_inst_61_, v_inst_62_, v_00_u03c0_63_);
lean_dec(v_inst_62_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___redArg___lam__0(lean_object* v_00_u03c0_65_, lean_object* v_toMul_66_, lean_object* v_toSub_67_, lean_object* v_toAddSemigroup_68_, lean_object* v_c_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_fst_71_; lean_object* v_snd_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_fst_71_ = lean_ctor_get(v_x_70_, 0);
lean_inc_n(v_fst_71_, 3);
v_snd_72_ = lean_ctor_get(v_x_70_, 1);
lean_inc_n(v_snd_72_, 2);
lean_dec_ref(v_x_70_);
lean_inc_n(v_c_69_, 2);
v___x_73_ = lean_apply_1(v_c_69_, v_snd_72_);
v___x_74_ = lean_apply_2(v_00_u03c0_65_, v_fst_71_, v___x_73_);
v___x_75_ = lean_apply_2(v_toMul_66_, v_fst_71_, v_snd_72_);
v___x_76_ = lean_apply_1(v_c_69_, v___x_75_);
v___x_77_ = lean_apply_2(v_toSub_67_, v___x_74_, v___x_76_);
v___x_78_ = lean_apply_1(v_c_69_, v_fst_71_);
v___x_79_ = lean_apply_2(v_toAddSemigroup_68_, v___x_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___redArg(lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_00_u03c0_82_){
_start:
{
lean_object* v_toAddMonoid_83_; lean_object* v_toSub_84_; lean_object* v_toAddSemigroup_85_; lean_object* v_toMonoid_86_; lean_object* v___x_87_; lean_object* v_toMul_88_; lean_object* v___f_89_; 
v_toAddMonoid_83_ = lean_ctor_get(v_inst_81_, 0);
lean_inc_ref(v_toAddMonoid_83_);
v_toSub_84_ = lean_ctor_get(v_inst_81_, 2);
lean_inc(v_toSub_84_);
lean_dec_ref(v_inst_81_);
v_toAddSemigroup_85_ = lean_ctor_get(v_toAddMonoid_83_, 0);
lean_inc(v_toAddSemigroup_85_);
lean_dec_ref(v_toAddMonoid_83_);
v_toMonoid_86_ = lean_ctor_get(v_inst_80_, 0);
v___x_87_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_86_);
v_toMul_88_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_toMul_88_);
lean_dec_ref(v___x_87_);
v___f_89_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_d1___redArg___lam__0), 6, 4);
lean_closure_set(v___f_89_, 0, v_00_u03c0_82_);
lean_closure_set(v___f_89_, 1, v_toMul_88_);
lean_closure_set(v___f_89_, 2, v_toSub_84_);
lean_closure_set(v___f_89_, 3, v_toAddSemigroup_85_);
return v___f_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___redArg___boxed(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_00_u03c0_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_ReciprocityTheory_Def_d1___redArg(v_inst_90_, v_inst_91_, v_00_u03c0_92_);
lean_dec_ref(v_inst_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1(lean_object* v_k_94_, lean_object* v_inst_95_, lean_object* v_G_96_, lean_object* v_inst_97_, lean_object* v_M_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_00_u03c0_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_tree_ReciprocityTheory_Def_d1___redArg(v_inst_97_, v_inst_99_, v_00_u03c0_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d1___boxed(lean_object* v_k_103_, lean_object* v_inst_104_, lean_object* v_G_105_, lean_object* v_inst_106_, lean_object* v_M_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_00_u03c0_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_tree_ReciprocityTheory_Def_d1(v_k_103_, v_inst_104_, v_G_105_, v_inst_106_, v_M_107_, v_inst_108_, v_inst_109_, v_00_u03c0_110_);
lean_dec(v_inst_109_);
lean_dec_ref(v_inst_106_);
lean_dec_ref(v_inst_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___redArg___lam__0(lean_object* v_00_u03c0_112_, lean_object* v_toMul_113_, lean_object* v_toSub_114_, lean_object* v_toAddSemigroup_115_, lean_object* v_z_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_snd_118_; lean_object* v_fst_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_147_; 
v_snd_118_ = lean_ctor_get(v_x_117_, 1);
v_fst_119_ = lean_ctor_get(v_x_117_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_117_);
if (v_isSharedCheck_147_ == 0)
{
v___x_121_ = v_x_117_;
v_isShared_122_ = v_isSharedCheck_147_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snd_118_);
lean_inc(v_fst_119_);
lean_dec(v_x_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_147_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_fst_123_; lean_object* v_snd_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_146_; 
v_fst_123_ = lean_ctor_get(v_snd_118_, 0);
v_snd_124_ = lean_ctor_get(v_snd_118_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_snd_118_);
if (v_isSharedCheck_146_ == 0)
{
v___x_126_ = v_snd_118_;
v_isShared_127_ = v_isSharedCheck_146_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_snd_124_);
lean_inc(v_fst_123_);
lean_dec(v_snd_118_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_146_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
lean_inc(v_snd_124_);
lean_inc(v_fst_123_);
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_fst_123_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_snd_124_);
v___x_129_ = v_reuseFailAlloc_145_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc(v_z_116_);
v___x_130_ = lean_apply_1(v_z_116_, v___x_129_);
lean_inc_n(v_fst_119_, 2);
v___x_131_ = lean_apply_2(v_00_u03c0_112_, v_fst_119_, v___x_130_);
lean_inc(v_toMul_113_);
lean_inc(v_fst_123_);
v___x_132_ = lean_apply_2(v_toMul_113_, v_fst_119_, v_fst_123_);
lean_inc(v_snd_124_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_snd_124_);
lean_ctor_set(v___x_121_, 0, v___x_132_);
v___x_134_ = v___x_121_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_snd_124_);
v___x_134_ = v_reuseFailAlloc_144_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_inc_n(v_z_116_, 2);
v___x_135_ = lean_apply_1(v_z_116_, v___x_134_);
lean_inc(v_toSub_114_);
v___x_136_ = lean_apply_2(v_toSub_114_, v___x_131_, v___x_135_);
lean_inc(v_fst_123_);
v___x_137_ = lean_apply_2(v_toMul_113_, v_fst_123_, v_snd_124_);
lean_inc(v_fst_119_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_fst_119_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_apply_1(v_z_116_, v___x_138_);
v___x_140_ = lean_apply_2(v_toAddSemigroup_115_, v___x_136_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_fst_119_);
lean_ctor_set(v___x_141_, 1, v_fst_123_);
v___x_142_ = lean_apply_1(v_z_116_, v___x_141_);
v___x_143_ = lean_apply_2(v_toSub_114_, v___x_140_, v___x_142_);
return v___x_143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___redArg(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_00_u03c0_150_){
_start:
{
lean_object* v_toAddMonoid_151_; lean_object* v_toSub_152_; lean_object* v_toAddSemigroup_153_; lean_object* v_toMonoid_154_; lean_object* v___x_155_; lean_object* v_toMul_156_; lean_object* v___f_157_; 
v_toAddMonoid_151_ = lean_ctor_get(v_inst_149_, 0);
lean_inc_ref(v_toAddMonoid_151_);
v_toSub_152_ = lean_ctor_get(v_inst_149_, 2);
lean_inc(v_toSub_152_);
lean_dec_ref(v_inst_149_);
v_toAddSemigroup_153_ = lean_ctor_get(v_toAddMonoid_151_, 0);
lean_inc(v_toAddSemigroup_153_);
lean_dec_ref(v_toAddMonoid_151_);
v_toMonoid_154_ = lean_ctor_get(v_inst_148_, 0);
v___x_155_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_154_);
v_toMul_156_ = lean_ctor_get(v___x_155_, 1);
lean_inc(v_toMul_156_);
lean_dec_ref(v___x_155_);
v___f_157_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_d2___redArg___lam__0), 6, 4);
lean_closure_set(v___f_157_, 0, v_00_u03c0_150_);
lean_closure_set(v___f_157_, 1, v_toMul_156_);
lean_closure_set(v___f_157_, 2, v_toSub_152_);
lean_closure_set(v___f_157_, 3, v_toAddSemigroup_153_);
return v___f_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___redArg___boxed(lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_00_u03c0_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_tree_ReciprocityTheory_Def_d2___redArg(v_inst_158_, v_inst_159_, v_00_u03c0_160_);
lean_dec_ref(v_inst_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2(lean_object* v_k_162_, lean_object* v_inst_163_, lean_object* v_G_164_, lean_object* v_inst_165_, lean_object* v_M_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_00_u03c0_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lp_tree_ReciprocityTheory_Def_d2___redArg(v_inst_165_, v_inst_167_, v_00_u03c0_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_d2___boxed(lean_object* v_k_171_, lean_object* v_inst_172_, lean_object* v_G_173_, lean_object* v_inst_174_, lean_object* v_M_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_00_u03c0_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lp_tree_ReciprocityTheory_Def_d2(v_k_171_, v_inst_172_, v_G_173_, v_inst_174_, v_M_175_, v_inst_176_, v_inst_177_, v_00_u03c0_178_);
lean_dec(v_inst_177_);
lean_dec_ref(v_inst_174_);
lean_dec_ref(v_inst_172_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z1(lean_object* v_k_180_, lean_object* v_inst_181_, lean_object* v_G_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_M_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_00_u03c0_188_, lean_object* v_N_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z1___boxed(lean_object* v_k_191_, lean_object* v_inst_192_, lean_object* v_G_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_M_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_00_u03c0_199_, lean_object* v_N_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = lp_tree_ReciprocityTheory_Def_Z1(v_k_191_, v_inst_192_, v_G_193_, v_inst_194_, v_inst_195_, v_M_196_, v_inst_197_, v_inst_198_, v_00_u03c0_199_, v_N_200_);
lean_dec(v_00_u03c0_199_);
lean_dec(v_inst_198_);
lean_dec_ref(v_inst_197_);
lean_dec_ref(v_inst_194_);
lean_dec_ref(v_inst_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B1(lean_object* v_k_202_, lean_object* v_inst_203_, lean_object* v_G_204_, lean_object* v_inst_205_, lean_object* v_M_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_00_u03c0_209_, lean_object* v_N_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B1___boxed(lean_object* v_k_212_, lean_object* v_inst_213_, lean_object* v_G_214_, lean_object* v_inst_215_, lean_object* v_M_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_00_u03c0_219_, lean_object* v_N_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_tree_ReciprocityTheory_Def_B1(v_k_212_, v_inst_213_, v_G_214_, v_inst_215_, v_M_216_, v_inst_217_, v_inst_218_, v_00_u03c0_219_, v_N_220_);
lean_dec(v_00_u03c0_219_);
lean_dec(v_inst_218_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_inst_215_);
lean_dec_ref(v_inst_213_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z2(lean_object* v_k_222_, lean_object* v_inst_223_, lean_object* v_G_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_M_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_00_u03c0_230_, lean_object* v_N_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(0);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_Z2___boxed(lean_object* v_k_233_, lean_object* v_inst_234_, lean_object* v_G_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_M_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_00_u03c0_241_, lean_object* v_N_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lp_tree_ReciprocityTheory_Def_Z2(v_k_233_, v_inst_234_, v_G_235_, v_inst_236_, v_inst_237_, v_M_238_, v_inst_239_, v_inst_240_, v_00_u03c0_241_, v_N_242_);
lean_dec(v_00_u03c0_241_);
lean_dec(v_inst_240_);
lean_dec_ref(v_inst_239_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_234_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B2(lean_object* v_k_244_, lean_object* v_inst_245_, lean_object* v_G_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_M_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_00_u03c0_252_, lean_object* v_N_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_B2___boxed(lean_object* v_k_255_, lean_object* v_inst_256_, lean_object* v_G_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_M_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_00_u03c0_263_, lean_object* v_N_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = lp_tree_ReciprocityTheory_Def_B2(v_k_255_, v_inst_256_, v_G_257_, v_inst_258_, v_inst_259_, v_M_260_, v_inst_261_, v_inst_262_, v_00_u03c0_263_, v_N_264_);
lean_dec(v_00_u03c0_263_);
lean_dec(v_inst_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_258_);
lean_dec_ref(v_inst_256_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__0(lean_object* v_inv_266_, lean_object* v___y_267_, lean_object* v_j_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_apply_2(v_inv_266_, v_j_268_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__1(lean_object* v_val_270_, lean_object* v___y_271_, lean_object* v_j_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_apply_2(v_val_270_, v___y_271_, v_j_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__2(lean_object* v___y_274_, lean_object* v_j_275_, lean_object* v_j_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_apply_2(v___y_274_, v_j_276_, v_j_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__3(lean_object* v___y_278_, lean_object* v___x_279_, lean_object* v_toMul_280_, lean_object* v_toAddCommMonoid_281_, lean_object* v___f_282_, lean_object* v_j_283_){
_start:
{
lean_object* v___f_284_; lean_object* v___x_285_; 
v___f_284_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__2), 3, 2);
lean_closure_set(v___f_284_, 0, v___y_278_);
lean_closure_set(v___f_284_, 1, v_j_283_);
v___x_285_ = lp_mathlib_dotProduct___redArg(v___x_279_, v_toMul_280_, v_toAddCommMonoid_281_, v___f_282_, v___f_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__3___boxed(lean_object* v___y_286_, lean_object* v___x_287_, lean_object* v_toMul_288_, lean_object* v_toAddCommMonoid_289_, lean_object* v___f_290_, lean_object* v_j_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__3(v___y_286_, v___x_287_, v_toMul_288_, v_toAddCommMonoid_289_, v___f_290_, v_j_291_);
lean_dec_ref(v_toAddCommMonoid_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__4(lean_object* v_rbar_293_, lean_object* v___x_294_, lean_object* v_toMul_295_, lean_object* v_toAddCommMonoid_296_, lean_object* v_g_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_301_; lean_object* v_val_302_; lean_object* v_inv_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___x_307_; 
v___x_301_ = lean_apply_1(v_rbar_293_, v_g_297_);
v_val_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_val_302_);
v_inv_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc(v_inv_303_);
lean_dec_ref(v___x_301_);
v___f_304_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__0), 3, 2);
lean_closure_set(v___f_304_, 0, v_inv_303_);
lean_closure_set(v___f_304_, 1, v___y_300_);
v___f_305_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__1), 3, 2);
lean_closure_set(v___f_305_, 0, v_val_302_);
lean_closure_set(v___f_305_, 1, v___y_299_);
lean_inc_ref(v_toAddCommMonoid_296_);
lean_inc(v_toMul_295_);
lean_inc(v___x_294_);
v___f_306_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_306_, 0, v___y_298_);
lean_closure_set(v___f_306_, 1, v___x_294_);
lean_closure_set(v___f_306_, 2, v_toMul_295_);
lean_closure_set(v___f_306_, 3, v_toAddCommMonoid_296_);
lean_closure_set(v___f_306_, 4, v___f_305_);
v___x_307_ = lp_mathlib_dotProduct___redArg(v___x_294_, v_toMul_295_, v_toAddCommMonoid_296_, v___f_306_, v___f_304_);
lean_dec_ref(v_toAddCommMonoid_296_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___redArg(lean_object* v_inst_308_, lean_object* v_n_309_, lean_object* v_rbar_310_){
_start:
{
lean_object* v_toSemiring_311_; lean_object* v_toAddCommMonoid_312_; lean_object* v___x_313_; lean_object* v_toMul_314_; lean_object* v___x_315_; lean_object* v___f_316_; 
v_toSemiring_311_ = lean_ctor_get(v_inst_308_, 0);
lean_inc_ref(v_toSemiring_311_);
lean_dec_ref(v_inst_308_);
v_toAddCommMonoid_312_ = lean_ctor_get(v_toSemiring_311_, 0);
lean_inc_ref(v_toAddCommMonoid_312_);
v___x_313_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_311_);
v_toMul_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_toMul_314_);
lean_dec_ref(v___x_313_);
v___x_315_ = l_List_finRange(v_n_309_);
v___f_316_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_Def_adRep___redArg___lam__4), 8, 4);
lean_closure_set(v___f_316_, 0, v_rbar_310_);
lean_closure_set(v___f_316_, 1, v___x_315_);
lean_closure_set(v___f_316_, 2, v_toMul_314_);
lean_closure_set(v___f_316_, 3, v_toAddCommMonoid_312_);
return v___f_316_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep(lean_object* v_k_317_, lean_object* v_inst_318_, lean_object* v_G_319_, lean_object* v_inst_320_, lean_object* v_n_321_, lean_object* v_rbar_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lp_tree_ReciprocityTheory_Def_adRep___redArg(v_inst_318_, v_n_321_, v_rbar_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Def_adRep___boxed(lean_object* v_k_324_, lean_object* v_inst_325_, lean_object* v_G_326_, lean_object* v_inst_327_, lean_object* v_n_328_, lean_object* v_rbar_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = lp_tree_ReciprocityTheory_Def_adRep(v_k_324_, v_inst_325_, v_G_326_, v_inst_327_, v_n_328_, v_rbar_329_);
lean_dec_ref(v_inst_327_);
return v_res_330_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_BasicDefinitions_ExistsUnique(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_BasicDefinitions_AdRep(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_BasicDefinitions_ExistsUnique(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
