// Lean compiler output
// Module: Lib.ClassField.GaloisCohomology.KummerCyclicClasses
// Imports: public import Init public meta import Init public import Lib.Adelic.Hecke.ClassSums public import Lib.ClassField.GaloisCohomology.ShapiroCorestriction public import Lib.ClassField.Places.LocalFields
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Additive_subNegMonoid___redArg(lean_object*);
lean_object* lp_mathlib_AddCommGroup_toIntModule___redArg(lean_object*);
lean_object* lp_GRH_New_instTopologicalSpaceDiscreteUnits___redArg();
lean_object* lp_GRH_New_unitsRep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TopologicalSpace_instCompleteLattice___redArg();
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoidHom_instAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_DivisionSemiring_toGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_Units_mk0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_unitsModule___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_unitsModule___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero___redArg(lean_object* v_inst_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_4_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_3_);
v___x_5_ = lp_mathlib_DivisionSemiring_toGroupWithZero___redArg(v___x_4_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_mathlib_Units_mk0___redArg(v___x_5_, v_a_2_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero___redArg___boxed(lean_object* v_inst_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_GRH_New_DiscreteUnits_ofNeZero___redArg(v_inst_7_, v_a_8_);
lean_dec_ref(v_inst_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero(lean_object* v_00_u03a9_10_, lean_object* v_inst_11_, lean_object* v_a_12_, lean_object* v_ha_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_GRH_New_DiscreteUnits_ofNeZero___redArg(v_inst_11_, v_a_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteUnits_ofNeZero___boxed(lean_object* v_00_u03a9_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_ha_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_GRH_New_DiscreteUnits_ofNeZero(v_00_u03a9_15_, v_inst_16_, v_a_17_, v_ha_18_);
lean_dec_ref(v_inst_16_);
return v_res_19_;
}
}
static lean_object* _init_lp_GRH_New_unitsModule___redArg___closed__0(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_GRH_New_instTopologicalSpaceDiscreteUnits___redArg();
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule___redArg(lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_toCommRing_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_toCommRing_24_ = lean_ctor_get(v_inst_22_, 0);
v___x_25_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_24_);
v___x_26_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_25_);
v___x_27_ = lp_mathlib_Additive_subNegMonoid___redArg(v___x_26_);
lean_inc_ref(v___x_27_);
v___x_28_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_27_);
v___x_29_ = lean_obj_once(&lp_GRH_New_unitsModule___redArg___closed__0, &lp_GRH_New_unitsModule___redArg___closed__0_once, _init_lp_GRH_New_unitsModule___redArg___closed__0);
v___x_30_ = lp_GRH_New_unitsRep___redArg(v_inst_21_, v_inst_22_, v_inst_23_);
v___x_31_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_31_, 0, v___x_27_);
lean_ctor_set(v___x_31_, 1, v___x_28_);
lean_ctor_set(v___x_31_, 2, v___x_29_);
lean_ctor_set(v___x_31_, 3, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule___redArg___boxed(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_GRH_New_unitsModule___redArg(v_inst_32_, v_inst_33_, v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule(lean_object* v_00_u0393_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_K_39_, lean_object* v_00_u03a9_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v_toCommRing_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_toCommRing_46_ = lean_ctor_get(v_inst_42_, 0);
v___x_47_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_46_);
v___x_48_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_47_);
v___x_49_ = lp_mathlib_Additive_subNegMonoid___redArg(v___x_48_);
lean_inc_ref(v___x_49_);
v___x_50_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_49_);
v___x_51_ = lean_obj_once(&lp_GRH_New_unitsModule___redArg___closed__0, &lp_GRH_New_unitsModule___redArg___closed__0_once, _init_lp_GRH_New_unitsModule___redArg___closed__0);
v___x_52_ = lp_GRH_New_unitsRep___redArg(v_inst_37_, v_inst_42_, v_inst_44_);
v___x_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_53_, 0, v___x_49_);
lean_ctor_set(v___x_53_, 1, v___x_50_);
lean_ctor_set(v___x_53_, 2, v___x_51_);
lean_ctor_set(v___x_53_, 3, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitsModule___boxed(lean_object* v_00_u0393_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_K_57_, lean_object* v_00_u03a9_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_unitsModule(v_00_u0393_54_, v_inst_55_, v_inst_56_, v_K_57_, v_00_u03a9_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_inst_62_, v_inst_63_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
lean_dec_ref(v_inst_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_GRH_New_pairingAnnihilator___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator(lean_object* v_A_69_, lean_object* v_B_70_, lean_object* v_C_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_b_75_, lean_object* v_L_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingAnnihilator___boxed(lean_object* v_A_78_, lean_object* v_B_79_, lean_object* v_C_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_b_84_, lean_object* v_L_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_pairingAnnihilator(v_A_78_, v_B_79_, v_C_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_b_84_, v_L_85_);
lean_dec(v_b_84_);
lean_dec_ref(v_inst_83_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
return v_res_86_;
}
}
static lean_object* _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__0(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_mathlib_TopologicalSpace_instCompleteLattice___redArg();
return v___x_87_;
}
}
static lean_object* _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__0, &lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__0_once, _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__0);
v___x_89_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg(){
_start:
{
lean_object* v___x_91_; lean_object* v_toOrderBot_92_; 
v___x_91_ = lean_obj_once(&lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__1, &lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__1_once, _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___closed__1);
v_toOrderBot_92_ = lean_ctor_get(v___x_91_, 2);
lean_inc(v_toOrderBot_92_);
return v_toOrderBot_92_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg___boxed(lean_object* v___dummy_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg();
return v_res_94_;
}
}
static lean_object* _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___redArg();
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib(lean_object* v_A_96_, lean_object* v_B_97_, lean_object* v_inst_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0, &lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0_once, _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___boxed(lean_object* v_A_101_, lean_object* v_B_102_, lean_object* v_inst_103_, lean_object* v_inst_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib(v_A_101_, v_B_102_, v_inst_103_, v_inst_104_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__0(lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_g_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_256__overap_111_; lean_object* v___x_112_; 
v___x_256__overap_111_ = lp_GRH_New_unitsRep___redArg(v_inst_106_, v_inst_107_, v_inst_108_);
v___x_112_ = lean_apply_2(v___x_256__overap_111_, v_g_109_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__0___boxed(lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_g_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__0(v_inst_113_, v_inst_114_, v_inst_115_, v_g_116_, v___y_117_);
lean_dec_ref(v_inst_114_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__1(lean_object* v_00_u03c1_119_, lean_object* v___x_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_apply_2(v_00_u03c1_119_, v___x_120_, v___y_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__2(lean_object* v_M_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_toInv_127_, lean_object* v_g_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_00_u03c1_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_136_; 
v_00_u03c1_131_ = lean_ctor_get(v_M_123_, 3);
lean_inc(v_00_u03c1_131_);
lean_dec_ref(v_M_123_);
lean_inc(v_g_128_);
v___f_132_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_132_, 0, v_inst_124_);
lean_closure_set(v___f_132_, 1, v_inst_125_);
lean_closure_set(v___f_132_, 2, v_inst_126_);
lean_closure_set(v___f_132_, 3, v_g_128_);
v___x_133_ = lean_apply_1(v_toInv_127_, v_g_128_);
v___f_134_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__1), 3, 2);
lean_closure_set(v___f_134_, 0, v_00_u03c1_131_);
lean_closure_set(v___f_134_, 1, v___x_133_);
v___f_135_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_135_, 0, v___f_134_);
lean_closure_set(v___f_135_, 1, v___y_129_);
v___x_136_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_135_, v___f_132_, v___y_130_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_M_140_){
_start:
{
lean_object* v_toCommRing_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_toInv_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_151_; 
v_toCommRing_141_ = lean_ctor_get(v_inst_138_, 0);
v___x_142_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_141_);
v___x_143_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_142_);
v___x_144_ = lp_mathlib_Additive_subNegMonoid___redArg(v___x_143_);
v___x_145_ = lp_mathlib_AddMonoidHom_instAddCommGroup___redArg(v___x_144_);
v___x_146_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_137_);
v_toInv_147_ = lean_ctor_get(v___x_146_, 1);
lean_inc(v_toInv_147_);
lean_dec_ref(v___x_146_);
lean_inc_ref(v___x_145_);
v___x_148_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_145_);
v___x_149_ = lean_obj_once(&lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0, &lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0_once, _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0);
v___f_150_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__2), 8, 5);
lean_closure_set(v___f_150_, 0, v_M_140_);
lean_closure_set(v___f_150_, 1, v_inst_137_);
lean_closure_set(v___f_150_, 2, v_inst_138_);
lean_closure_set(v___f_150_, 3, v_inst_139_);
lean_closure_set(v___f_150_, 4, v_toInv_147_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v___x_148_);
lean_ctor_set(v___x_151_, 2, v___x_149_);
lean_ctor_set(v___x_151_, 3, v___f_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual(lean_object* v_R_152_, lean_object* v_00_u0393_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_K_157_, lean_object* v_00_u03a9_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_M_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v_toCommRing_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_toInv_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v_toCommRing_166_ = lean_ctor_get(v_inst_160_, 0);
v___x_167_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_166_);
v___x_168_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_167_);
v___x_169_ = lp_mathlib_Additive_subNegMonoid___redArg(v___x_168_);
v___x_170_ = lp_mathlib_AddMonoidHom_instAddCommGroup___redArg(v___x_169_);
v___x_171_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_155_);
v_toInv_172_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_toInv_172_);
lean_dec_ref(v___x_171_);
lean_inc_ref(v___x_170_);
v___x_173_ = lp_mathlib_AddCommGroup_toIntModule___redArg(v___x_170_);
v___x_174_ = lean_obj_once(&lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0, &lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0_once, _init_lp_GRH_New_instTopologicalSpaceAddMonoidHom__lib___closed__0);
v___f_175_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteModule_cartierDual___redArg___lam__2), 8, 5);
lean_closure_set(v___f_175_, 0, v_M_164_);
lean_closure_set(v___f_175_, 1, v_inst_155_);
lean_closure_set(v___f_175_, 2, v_inst_160_);
lean_closure_set(v___f_175_, 3, v_inst_162_);
lean_closure_set(v___f_175_, 4, v_toInv_172_);
v___x_176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_176_, 0, v___x_170_);
lean_ctor_set(v___x_176_, 1, v___x_173_);
lean_ctor_set(v___x_176_, 2, v___x_174_);
lean_ctor_set(v___x_176_, 3, v___f_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_cartierDual___boxed(lean_object* v_R_177_, lean_object* v_00_u0393_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_K_182_, lean_object* v_00_u03a9_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_M_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_GRH_New_DiscreteModule_cartierDual(v_R_177_, v_00_u0393_178_, v_inst_179_, v_inst_180_, v_inst_181_, v_K_182_, v_00_u03a9_183_, v_inst_184_, v_inst_185_, v_inst_186_, v_inst_187_, v_inst_188_, v_M_189_, v_inst_190_);
lean_dec_ref(v_inst_186_);
lean_dec_ref(v_inst_184_);
lean_dec_ref(v_inst_179_);
return v_res_191_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Hecke_ClassSums(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GaloisCohomology_ShapiroCorestriction(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_LocalFields(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_GaloisCohomology_KummerCyclicClasses(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Hecke_ClassSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_GaloisCohomology_ShapiroCorestriction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Places_LocalFields(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
