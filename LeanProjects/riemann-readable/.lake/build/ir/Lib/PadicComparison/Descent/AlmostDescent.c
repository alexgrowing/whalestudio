// Lean compiler output
// Module: Lib.PadicComparison.Descent.AlmostDescent
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.RelativeChains public import Lib.General.Algebra.PerfectAlgebras
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
lean_object* lp_mathlib_CommAlgCat_instCategory___redArg();
lean_object* lp_mathlib_CategoryTheory_ObjectProperty_FullSubcategory_category___redArg(lean_object*);
lean_object* lp_GRH_New_Variety_reprFunctor___redArg(lean_object*);
lean_object* lp_GRH_New_Variety_relFreeAb___redArg(lean_object*);
lean_object* lp_mathlib_ModuleCat_MonoidalCategory_instMonoidalCategoryStruct___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_MonoidalCategory_curriedTensor___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_whiskerLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SMulWithZero_compHom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAbOfHom___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAbOfHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAbOfHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_00_u03a6_6_, lean_object* v_f_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_map_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_20_; 
v___x_8_ = lp_mathlib_ModuleCat_MonoidalCategory_instMonoidalCategoryStruct___redArg(v_inst_1_);
v___x_9_ = lp_mathlib_CategoryTheory_MonoidalCategory_curriedTensor___redArg(v___x_8_);
v_map_10_ = lean_ctor_get(v___x_9_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_20_ == 0)
{
lean_object* v_unused_21_; 
v_unused_21_ = lean_ctor_get(v___x_9_, 0);
lean_dec(v_unused_21_);
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_20_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_map_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_20_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v_inst_4_);
lean_ctor_set(v___x_12_, 0, v_inst_2_);
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_inst_2_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_inst_4_);
v___x_15_ = v_reuseFailAlloc_19_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___f_18_; 
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_inst_3_);
lean_ctor_set(v___x_16_, 1, v_inst_5_);
v___x_17_ = lean_apply_3(v_map_10_, v___x_15_, v___x_16_, v_f_7_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_Functor_whiskerLeft___redArg___lam__0), 3, 2);
lean_closure_set(v___f_18_, 0, v_00_u03a6_6_);
lean_closure_set(v___f_18_, 1, v___x_17_);
return v___f_18_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap(lean_object* v_S_22_, lean_object* v_M_23_, lean_object* v_M_x27_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_C_30_, lean_object* v_inst_31_, lean_object* v_00_u03a6_32_, lean_object* v_f_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap___redArg(v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_00_u03a6_32_, v_f_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap___boxed(lean_object* v_S_35_, lean_object* v_M_36_, lean_object* v_M_x27_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_C_43_, lean_object* v_inst_44_, lean_object* v_00_u03a6_45_, lean_object* v_f_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_GRH___private_Lib_PadicComparison_Descent_AlmostDescent_0__New_Variety_tensorCoeffMap(v_S_35_, v_M_36_, v_M_x27_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_C_43_, v_inst_44_, v_00_u03a6_45_, v_f_46_);
lean_dec_ref(v_inst_44_);
return v_res_47_;
}
}
static lean_object* _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_mathlib_CommAlgCat_instCategory___redArg();
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__0, &lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__0_once, _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__0);
v___x_50_ = lp_mathlib_CategoryTheory_ObjectProperty_FullSubcategory_category___redArg(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__1, &lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__1_once, _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__1);
v___x_52_ = lp_GRH_New_Variety_reprFunctor___redArg(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAbOfHom___redArg(lean_object* v_b_53_){
_start:
{
lean_object* v___x_54_; lean_object* v_obj_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2, &lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2_once, _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2);
v_obj_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_obj_55_);
v___x_56_ = lean_apply_1(v_obj_55_, v_b_53_);
v___x_57_ = lp_GRH_New_Variety_relFreeAb___redArg(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAbOfHom(lean_object* v_p_58_, lean_object* v_inst_59_, lean_object* v_S_60_, lean_object* v_inst_61_, lean_object* v_b_62_, lean_object* v_d_63_, lean_object* v_00_u03c6_64_){
_start:
{
lean_object* v___x_65_; lean_object* v_obj_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2, &lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2_once, _init_lp_GRH_New_Variety_relFreeAbOfHom___redArg___closed__2);
v_obj_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_obj_66_);
v___x_67_ = lean_apply_1(v_obj_66_, v_b_62_);
v___x_68_ = lp_GRH_New_Variety_relFreeAb___redArg(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAbOfHom___boxed(lean_object* v_p_69_, lean_object* v_inst_70_, lean_object* v_S_71_, lean_object* v_inst_72_, lean_object* v_b_73_, lean_object* v_d_74_, lean_object* v_00_u03c6_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_Variety_relFreeAbOfHom(v_p_69_, v_inst_70_, v_S_71_, v_inst_72_, v_b_73_, v_d_74_, v_00_u03c6_75_);
lean_dec(v_00_u03c6_75_);
lean_dec_ref(v_d_74_);
lean_dec_ref(v_inst_72_);
lean_dec(v_p_69_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing___redArg(lean_object* v_a_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v_algebra_79_; lean_object* v_algebraMap_80_; lean_object* v_toSMul_81_; lean_object* v_algebraMap_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_91_; 
v_algebra_79_ = lean_ctor_get(v_a_77_, 1);
lean_inc_ref(v_algebra_79_);
lean_dec_ref(v_a_77_);
v_algebraMap_80_ = lean_ctor_get(v_inst_78_, 1);
lean_inc(v_algebraMap_80_);
lean_dec_ref(v_inst_78_);
v_toSMul_81_ = lean_ctor_get(v_algebra_79_, 0);
v_algebraMap_82_ = lean_ctor_get(v_algebra_79_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_algebra_79_);
if (v_isSharedCheck_91_ == 0)
{
v___x_84_ = v_algebra_79_;
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_algebraMap_82_);
lean_inc(v_toSMul_81_);
lean_dec(v_algebra_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_89_; 
lean_inc(v_algebraMap_80_);
v___f_86_ = lean_alloc_closure((void*)(lp_mathlib_SMulWithZero_compHom___redArg___lam__0), 4, 2);
lean_closure_set(v___f_86_, 0, v_algebraMap_80_);
lean_closure_set(v___f_86_, 1, v_toSMul_81_);
v___f_87_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_87_, 0, v_algebraMap_80_);
lean_closure_set(v___f_87_, 1, v_algebraMap_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___f_87_);
lean_ctor_set(v___x_84_, 0, v___f_86_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___f_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing(lean_object* v_p_92_, lean_object* v_inst_93_, lean_object* v_S_94_, lean_object* v_V_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_a_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing___redArg(v_a_98_, v_inst_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing___boxed(lean_object* v_p_101_, lean_object* v_inst_102_, lean_object* v_S_103_, lean_object* v_V_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_a_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_GRH_New_Variety_instAlgebraCarrierObjCommAlgPerfectRing(v_p_101_, v_inst_102_, v_S_103_, v_V_104_, v_inst_105_, v_inst_106_, v_a_107_, v_inst_108_);
lean_dec_ref(v_inst_106_);
lean_dec_ref(v_inst_105_);
lean_dec(v_p_101_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong___redArg___lam__0(lean_object* v_00_u03c6_110_, lean_object* v_toMul_111_, lean_object* v_c_112_, lean_object* v_x_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_apply_1(v_00_u03c6_110_, v_c_112_);
v___x_115_ = lean_apply_2(v_toMul_111_, v___x_114_, v_x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong___redArg(lean_object* v_d_116_, lean_object* v_00_u03c6_117_){
_start:
{
lean_object* v_commRing_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_137_; 
v_commRing_118_ = lean_ctor_get(v_d_116_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v_d_116_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v_d_116_, 1);
lean_dec(v_unused_138_);
v___x_120_ = v_d_116_;
v_isShared_121_ = v_isSharedCheck_137_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_commRing_118_);
lean_dec(v_d_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_137_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_toSemiring_122_; lean_object* v___x_123_; lean_object* v_toMul_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_135_; 
v_toSemiring_122_ = lean_ctor_get(v_commRing_118_, 0);
lean_inc_ref(v_toSemiring_122_);
v___x_123_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_122_);
v_toMul_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v___x_123_, 1);
lean_dec(v_unused_136_);
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_135_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_toMul_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_135_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___f_128_; lean_object* v___x_130_; 
lean_inc(v_00_u03c6_117_);
v___f_128_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_perfectAlgAlong___redArg___lam__0), 4, 2);
lean_closure_set(v___f_128_, 0, v_00_u03c6_117_);
lean_closure_set(v___f_128_, 1, v_toMul_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_00_u03c6_117_);
lean_ctor_set(v___x_126_, 0, v___f_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___f_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_00_u03c6_117_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_130_);
v___x_132_ = v___x_120_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_commRing_118_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong(lean_object* v_p_139_, lean_object* v_inst_140_, lean_object* v_S_141_, lean_object* v_inst_142_, lean_object* v_b_143_, lean_object* v_d_144_, lean_object* v_00_u03c6_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lp_GRH_New_Variety_perfectAlgAlong___redArg(v_d_144_, v_00_u03c6_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_perfectAlgAlong___boxed(lean_object* v_p_147_, lean_object* v_inst_148_, lean_object* v_S_149_, lean_object* v_inst_150_, lean_object* v_b_151_, lean_object* v_d_152_, lean_object* v_00_u03c6_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_GRH_New_Variety_perfectAlgAlong(v_p_147_, v_inst_148_, v_S_149_, v_inst_150_, v_b_151_, v_d_152_, v_00_u03c6_153_);
lean_dec_ref(v_b_151_);
lean_dec_ref(v_inst_150_);
lean_dec(v_p_147_);
return v_res_154_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_RelativeChains(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_PerfectAlgebras(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicComparison_Descent_AlmostDescent(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_RelativeChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_PerfectAlgebras(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
