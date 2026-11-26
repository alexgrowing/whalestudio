// Lean compiler output
// Module: Lib.Cohomology.Hodge.CupProduct
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.BijectiveComparisons
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
extern lean_object* lp_mathlib_Int_instCommSemiring;
lean_object* lp_mathlib_AddCommGroup_toIntModule___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_addCommGroup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_AddCommGrpCat_instCategory;
lean_object* lp_mathlib_CategoryTheory_Functor_category___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_curryObj___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_abTensorMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_abTensorMap___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_abTensorMap___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensorMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensorMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_abTensor___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_abTensor___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_abTensor___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_abTensor___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_Variety_abTensor___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_abTensor___redArg___closed__2;
static lean_once_cell_t lp_GRH_New_Variety_abTensor___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_abTensor___redArg___closed__3;
static lean_once_cell_t lp_GRH_New_Variety_abTensor___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_abTensor___redArg___closed__4;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_abTensor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_abTensor___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensorMap___redArg(lean_object* v_B_2_, lean_object* v_A_x27_3_, lean_object* v_B_x27_4_, lean_object* v_f_5_, lean_object* v_g_6_){
_start:
{
lean_object* v___x_7_; lean_object* v_toAddMonoid_8_; lean_object* v_toAddMonoid_9_; lean_object* v_toAddMonoid_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___f_18_; 
v___x_7_ = lp_mathlib_Int_instCommSemiring;
v_toAddMonoid_8_ = lean_ctor_get(v_B_2_, 0);
lean_inc_ref(v_toAddMonoid_8_);
v_toAddMonoid_9_ = lean_ctor_get(v_B_x27_4_, 0);
lean_inc_ref(v_toAddMonoid_9_);
v_toAddMonoid_10_ = lean_ctor_get(v_A_x27_3_, 0);
lean_inc_ref(v_toAddMonoid_10_);
v___x_11_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v_B_2_);
v___x_12_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v_A_x27_3_);
v___x_13_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v_B_x27_4_);
v___f_14_ = ((lean_object*)(lp_GRH_New_Variety_abTensorMap___redArg___closed__0));
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_15_, 0, v_f_5_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_16_, 0, v_g_6_);
v___x_17_ = lp_mathlib_TensorProduct_map___redArg(v___x_7_, v___x_7_, v___f_14_, v_toAddMonoid_8_, v_toAddMonoid_10_, v_toAddMonoid_9_, v___x_11_, v___x_12_, v___x_13_, v___f_15_, v___f_16_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_18_, 0, v___x_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensorMap(lean_object* v_A_19_, lean_object* v_B_20_, lean_object* v_A_x27_21_, lean_object* v_B_x27_22_, lean_object* v_f_23_, lean_object* v_g_24_){
_start:
{
lean_object* v___x_25_; lean_object* v_toAddMonoid_26_; lean_object* v_toAddMonoid_27_; lean_object* v_toAddMonoid_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___f_36_; 
v___x_25_ = lp_mathlib_Int_instCommSemiring;
v_toAddMonoid_26_ = lean_ctor_get(v_B_20_, 0);
lean_inc_ref(v_toAddMonoid_26_);
v_toAddMonoid_27_ = lean_ctor_get(v_B_x27_22_, 0);
lean_inc_ref(v_toAddMonoid_27_);
v_toAddMonoid_28_ = lean_ctor_get(v_A_x27_21_, 0);
lean_inc_ref(v_toAddMonoid_28_);
v___x_29_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v_B_20_);
v___x_30_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v_A_x27_21_);
v___x_31_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v_B_x27_22_);
v___f_32_ = ((lean_object*)(lp_GRH_New_Variety_abTensorMap___redArg___closed__0));
v___f_33_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_33_, 0, v_f_23_);
v___f_34_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_34_, 0, v_g_24_);
v___x_35_ = lp_mathlib_TensorProduct_map___redArg(v___x_25_, v___x_25_, v___f_32_, v_toAddMonoid_26_, v_toAddMonoid_28_, v_toAddMonoid_27_, v___x_29_, v___x_30_, v___x_31_, v___f_33_, v___f_34_);
v___f_36_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_36_, 0, v___x_35_);
return v___f_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensorMap___boxed(lean_object* v_A_37_, lean_object* v_B_38_, lean_object* v_A_x27_39_, lean_object* v_B_x27_40_, lean_object* v_f_41_, lean_object* v_g_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_GRH_New_Variety_abTensorMap(v_A_37_, v_B_38_, v_A_x27_39_, v_B_x27_40_, v_f_41_, v_g_42_);
lean_dec_ref(v_A_37_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__0(lean_object* v_p_44_, lean_object* v___x_45_, lean_object* v_c_46_){
_start:
{
lean_object* v_fst_47_; lean_object* v_snd_48_; lean_object* v_obj_49_; lean_object* v___x_50_; lean_object* v_obj_51_; lean_object* v___x_52_; lean_object* v_toAddMonoid_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_fst_47_ = lean_ctor_get(v_p_44_, 0);
lean_inc(v_fst_47_);
v_snd_48_ = lean_ctor_get(v_p_44_, 1);
lean_inc(v_snd_48_);
lean_dec_ref(v_p_44_);
v_obj_49_ = lean_ctor_get(v_fst_47_, 0);
lean_inc(v_obj_49_);
lean_dec(v_fst_47_);
lean_inc(v_c_46_);
v___x_50_ = lean_apply_1(v_obj_49_, v_c_46_);
v_obj_51_ = lean_ctor_get(v_snd_48_, 0);
lean_inc(v_obj_51_);
lean_dec(v_snd_48_);
v___x_52_ = lean_apply_1(v_obj_51_, v_c_46_);
v_toAddMonoid_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc_ref(v_toAddMonoid_53_);
lean_inc_ref(v___x_50_);
v___x_54_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_50_);
v___x_55_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_52_);
v___x_56_ = lp_mathlib_TensorProduct_addCommGroup___redArg(v___x_45_, v___x_50_, v_toAddMonoid_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__1(lean_object* v_p_57_, lean_object* v___x_58_, lean_object* v_X_59_, lean_object* v_Y_60_, lean_object* v_f_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v_obj_65_; lean_object* v_map_66_; lean_object* v_obj_67_; lean_object* v_map_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_toAddMonoid_72_; lean_object* v_toAddMonoid_73_; lean_object* v_toAddMonoid_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_415__overap_83_; lean_object* v___x_84_; 
v_fst_63_ = lean_ctor_get(v_p_57_, 0);
lean_inc(v_fst_63_);
v_snd_64_ = lean_ctor_get(v_p_57_, 1);
lean_inc(v_snd_64_);
lean_dec_ref(v_p_57_);
v_obj_65_ = lean_ctor_get(v_fst_63_, 0);
lean_inc(v_obj_65_);
v_map_66_ = lean_ctor_get(v_fst_63_, 1);
lean_inc(v_map_66_);
lean_dec(v_fst_63_);
v_obj_67_ = lean_ctor_get(v_snd_64_, 0);
lean_inc_n(v_obj_67_, 2);
v_map_68_ = lean_ctor_get(v_snd_64_, 1);
lean_inc(v_map_68_);
lean_dec(v_snd_64_);
lean_inc_n(v_X_59_, 2);
v___x_69_ = lean_apply_1(v_obj_67_, v_X_59_);
lean_inc_n(v_Y_60_, 3);
v___x_70_ = lean_apply_1(v_obj_65_, v_Y_60_);
v___x_71_ = lean_apply_1(v_obj_67_, v_Y_60_);
v_toAddMonoid_72_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_toAddMonoid_72_);
v_toAddMonoid_73_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_toAddMonoid_73_);
v_toAddMonoid_74_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_toAddMonoid_74_);
lean_inc(v_f_61_);
v___x_75_ = lean_apply_3(v_map_66_, v_X_59_, v_Y_60_, v_f_61_);
v___x_76_ = lean_apply_3(v_map_68_, v_X_59_, v_Y_60_, v_f_61_);
v___x_77_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_69_);
v___x_78_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_70_);
v___x_79_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_71_);
v___f_80_ = ((lean_object*)(lp_GRH_New_Variety_abTensorMap___redArg___closed__0));
v___f_81_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_81_, 0, v___x_75_);
v___f_82_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_82_, 0, v___x_76_);
lean_inc_ref(v___x_58_);
v___x_415__overap_83_ = lp_mathlib_TensorProduct_map___redArg(v___x_58_, v___x_58_, v___f_80_, v_toAddMonoid_72_, v_toAddMonoid_74_, v_toAddMonoid_73_, v___x_77_, v___x_78_, v___x_79_, v___f_81_, v___f_82_);
v___x_84_ = lean_apply_1(v___x_415__overap_83_, v___y_62_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__2(lean_object* v___x_85_, lean_object* v_p_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_89_; 
lean_inc_ref(v___x_85_);
lean_inc_ref(v_p_86_);
v___f_87_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abTensor___redArg___lam__0), 3, 2);
lean_closure_set(v___f_87_, 0, v_p_86_);
lean_closure_set(v___f_87_, 1, v___x_85_);
v___f_88_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abTensor___redArg___lam__1), 6, 2);
lean_closure_set(v___f_88_, 0, v_p_86_);
lean_closure_set(v___f_88_, 1, v___x_85_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v___f_87_);
lean_ctor_set(v___x_89_, 1, v___f_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___lam__3(lean_object* v___x_90_, lean_object* v_X_91_, lean_object* v_Y_92_, lean_object* v_f_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_snd_95_; lean_object* v_obj_96_; lean_object* v___x_97_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v_obj_100_; lean_object* v___x_101_; lean_object* v_obj_102_; lean_object* v___x_103_; lean_object* v_fst_104_; lean_object* v_snd_105_; lean_object* v_toAddMonoid_106_; lean_object* v_toAddMonoid_107_; lean_object* v_toAddMonoid_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___f_118_; 
v_snd_95_ = lean_ctor_get(v_X_91_, 1);
lean_inc(v_snd_95_);
lean_dec_ref(v_X_91_);
v_obj_96_ = lean_ctor_get(v_snd_95_, 0);
lean_inc(v_obj_96_);
lean_dec(v_snd_95_);
lean_inc_n(v___y_94_, 4);
v___x_97_ = lean_apply_1(v_obj_96_, v___y_94_);
v_fst_98_ = lean_ctor_get(v_Y_92_, 0);
lean_inc(v_fst_98_);
v_snd_99_ = lean_ctor_get(v_Y_92_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v_Y_92_);
v_obj_100_ = lean_ctor_get(v_fst_98_, 0);
lean_inc(v_obj_100_);
lean_dec(v_fst_98_);
v___x_101_ = lean_apply_1(v_obj_100_, v___y_94_);
v_obj_102_ = lean_ctor_get(v_snd_99_, 0);
lean_inc(v_obj_102_);
lean_dec(v_snd_99_);
v___x_103_ = lean_apply_1(v_obj_102_, v___y_94_);
v_fst_104_ = lean_ctor_get(v_f_93_, 0);
lean_inc(v_fst_104_);
v_snd_105_ = lean_ctor_get(v_f_93_, 1);
lean_inc(v_snd_105_);
lean_dec_ref(v_f_93_);
v_toAddMonoid_106_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_toAddMonoid_106_);
v_toAddMonoid_107_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_toAddMonoid_107_);
v_toAddMonoid_108_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_toAddMonoid_108_);
v___x_109_ = lean_apply_1(v_fst_104_, v___y_94_);
v___x_110_ = lean_apply_1(v_snd_105_, v___y_94_);
v___x_111_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_97_);
v___x_112_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_101_);
v___x_113_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_103_);
v___f_114_ = ((lean_object*)(lp_GRH_New_Variety_abTensorMap___redArg___closed__0));
v___f_115_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_115_, 0, v___x_109_);
v___f_116_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_116_, 0, v___x_110_);
lean_inc_ref(v___x_90_);
v___x_117_ = lp_mathlib_TensorProduct_map___redArg(v___x_90_, v___x_90_, v___f_114_, v_toAddMonoid_106_, v_toAddMonoid_108_, v_toAddMonoid_107_, v___x_111_, v___x_112_, v___x_113_, v___f_115_, v___f_116_);
v___f_118_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_118_, 0, v___x_117_);
return v___f_118_;
}
}
static lean_object* _init_lp_GRH_New_Variety_abTensor___redArg___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___f_120_; 
v___x_119_ = lp_mathlib_Int_instCommSemiring;
v___f_120_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abTensor___redArg___lam__2), 2, 1);
lean_closure_set(v___f_120_, 0, v___x_119_);
return v___f_120_;
}
}
static lean_object* _init_lp_GRH_New_Variety_abTensor___redArg___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v___f_122_; 
v___x_121_ = lp_mathlib_Int_instCommSemiring;
v___f_122_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abTensor___redArg___lam__3), 5, 1);
lean_closure_set(v___f_122_, 0, v___x_121_);
return v___f_122_;
}
}
static lean_object* _init_lp_GRH_New_Variety_abTensor___redArg___closed__2(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lp_mathlib_AddCommGrpCat_instCategory;
v___x_124_ = lp_mathlib_CategoryTheory_Functor_category___redArg(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_lp_GRH_New_Variety_abTensor___redArg___closed__3(void){
_start:
{
lean_object* v___f_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v___f_125_ = lean_obj_once(&lp_GRH_New_Variety_abTensor___redArg___closed__1, &lp_GRH_New_Variety_abTensor___redArg___closed__1_once, _init_lp_GRH_New_Variety_abTensor___redArg___closed__1);
v___f_126_ = lean_obj_once(&lp_GRH_New_Variety_abTensor___redArg___closed__0, &lp_GRH_New_Variety_abTensor___redArg___closed__0_once, _init_lp_GRH_New_Variety_abTensor___redArg___closed__0);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___f_126_);
lean_ctor_set(v___x_127_, 1, v___f_125_);
return v___x_127_;
}
}
static lean_object* _init_lp_GRH_New_Variety_abTensor___redArg___closed__4(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&lp_GRH_New_Variety_abTensor___redArg___closed__3, &lp_GRH_New_Variety_abTensor___redArg___closed__3_once, _init_lp_GRH_New_Variety_abTensor___redArg___closed__3);
v___x_129_ = lean_obj_once(&lp_GRH_New_Variety_abTensor___redArg___closed__2, &lp_GRH_New_Variety_abTensor___redArg___closed__2_once, _init_lp_GRH_New_Variety_abTensor___redArg___closed__2);
v___x_130_ = lp_mathlib_CategoryTheory_Functor_curryObj___redArg(v___x_129_, v___x_129_, v___x_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg(){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&lp_GRH_New_Variety_abTensor___redArg___closed__4, &lp_GRH_New_Variety_abTensor___redArg___closed__4_once, _init_lp_GRH_New_Variety_abTensor___redArg___closed__4);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___redArg___boxed(lean_object* v___dummy_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_GRH_New_Variety_abTensor___redArg();
return v_res_134_;
}
}
static lean_object* _init_lp_GRH_New_Variety_abTensor___closed__0(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lp_GRH_New_Variety_abTensor___redArg();
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor(lean_object* v_C_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&lp_GRH_New_Variety_abTensor___closed__0, &lp_GRH_New_Variety_abTensor___closed__0_once, _init_lp_GRH_New_Variety_abTensor___closed__0);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_abTensor___boxed(lean_object* v_C_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_GRH_New_Variety_abTensor(v_C_139_, v_inst_140_);
lean_dec_ref(v_inst_140_);
return v_res_141_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_BijectiveComparisons(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_Hodge_CupProduct(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_BijectiveComparisons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
