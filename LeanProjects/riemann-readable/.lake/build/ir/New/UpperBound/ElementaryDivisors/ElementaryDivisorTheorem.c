// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.ElementaryDivisorTheorem
// Imports: public import Init public meta import Init public import New.Reduction.Lattices.Colength public import New.UpperBound.ElementaryDivisors.AveragingMap public import New.UpperBound.ElementaryDivisors.DefectCount public import New.UpperBound.ElementaryDivisors.Depth
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
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_blockDiagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_kroneckerMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_regroup___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_regroup___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_regroup___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_regroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_regroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_edgewise___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_edgewise___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_edgewise(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_valuedIn___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn(lean_object* v_O_5_, lean_object* v_X_6_, lean_object* v_I_7_, lean_object* v_inst_8_, lean_object* v_C_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_valuedIn___boxed(lean_object* v_O_11_, lean_object* v_X_12_, lean_object* v_I_13_, lean_object* v_inst_14_, lean_object* v_C_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_valuedIn(v_O_11_, v_X_12_, v_I_13_, v_inst_14_, v_C_15_);
lean_dec_ref(v_inst_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_regroup___redArg___lam__0(lean_object* v_J_17_, lean_object* v_x_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_toFun_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_37_; 
v_toFun_20_ = lean_ctor_get(v_J_17_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v_J_17_);
if (v_isSharedCheck_37_ == 0)
{
lean_object* v_unused_38_; 
v_unused_38_ = lean_ctor_get(v_J_17_, 1);
lean_dec(v_unused_38_);
v___x_22_ = v_J_17_;
v_isShared_23_ = v_isSharedCheck_37_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_toFun_20_);
lean_dec(v_J_17_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_37_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v_fst_25_; lean_object* v_snd_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_36_; 
v___x_24_ = lean_apply_1(v_toFun_20_, v_i_19_);
v_fst_25_ = lean_ctor_get(v___x_24_, 0);
v_snd_26_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_36_ == 0)
{
v___x_28_ = v___x_24_;
v_isShared_29_ = v_isSharedCheck_36_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_snd_26_);
lean_inc(v_fst_25_);
lean_dec(v___x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_36_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v_x_18_);
lean_ctor_set(v___x_28_, 0, v_snd_26_);
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_snd_26_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_x_18_);
v___x_31_ = v_reuseFailAlloc_35_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_33_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v_fst_25_);
lean_ctor_set(v___x_22_, 0, v___x_31_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_fst_25_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_regroup___redArg___lam__1(lean_object* v_J_39_, lean_object* v_x_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
v___f_43_ = lean_alloc_closure((void*)(lp_GRH_New_regroup___redArg___lam__0), 3, 2);
lean_closure_set(v___f_43_, 0, v_J_39_);
lean_closure_set(v___f_43_, 1, v_x_40_);
v___x_44_ = lp_mathlib_LinearMap_funLeft___redArg___lam__0(v___f_43_, v___y_41_, v___y_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_regroup___redArg(lean_object* v_J_45_){
_start:
{
lean_object* v___f_46_; lean_object* v___f_47_; 
v___f_46_ = lean_alloc_closure((void*)(lp_GRH_New_regroup___redArg___lam__1), 4, 1);
lean_closure_set(v___f_46_, 0, v_J_45_);
v___f_47_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_47_, 0, v___f_46_);
return v___f_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_regroup(lean_object* v_O_48_, lean_object* v_X_49_, lean_object* v_H_50_, lean_object* v_I_51_, lean_object* v_L_52_, lean_object* v_inst_53_, lean_object* v_J_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_GRH_New_regroup___redArg(v_J_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_regroup___boxed(lean_object* v_O_56_, lean_object* v_X_57_, lean_object* v_H_58_, lean_object* v_I_59_, lean_object* v_L_60_, lean_object* v_inst_61_, lean_object* v_J_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_GRH_New_regroup(v_O_56_, v_X_57_, v_H_58_, v_I_59_, v_L_60_, v_inst_61_, v_J_62_);
lean_dec_ref(v_inst_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_edgewise___redArg___lam__0(lean_object* v_toMul_64_, lean_object* v_x1_65_, lean_object* v_x2_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_2(v_toMul_64_, v_x1_65_, v_x2_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_edgewise___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_u_70_, lean_object* v_A_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_toSemiring_74_; lean_object* v___x_75_; lean_object* v_toMul_76_; lean_object* v___x_77_; lean_object* v_toZero_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_toSemiring_74_ = lean_ctor_get(v_inst_68_, 0);
lean_inc_ref_n(v_toSemiring_74_, 2);
lean_dec_ref(v_inst_68_);
v___x_75_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_74_);
v_toMul_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_toMul_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_74_);
v_toZero_78_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_toZero_78_);
lean_dec_ref(v___x_77_);
v___f_79_ = lean_alloc_closure((void*)(lp_GRH_New_edgewise___redArg___lam__0), 3, 1);
lean_closure_set(v___f_79_, 0, v_toMul_76_);
v___x_80_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_blockDiagonal), 9, 7);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, lean_box(0));
lean_closure_set(v___x_80_, 2, lean_box(0));
lean_closure_set(v___x_80_, 3, lean_box(0));
lean_closure_set(v___x_80_, 4, v_inst_69_);
lean_closure_set(v___x_80_, 5, v_toZero_78_);
lean_closure_set(v___x_80_, 6, v_u_70_);
v___x_81_ = lp_mathlib_Matrix_kroneckerMap___redArg(v___f_79_, v___x_80_, v_A_71_, v_a_72_, v_a_73_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_edgewise(lean_object* v_O_82_, lean_object* v_H_83_, lean_object* v_Ed_84_, lean_object* v_L_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_u_88_, lean_object* v_A_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_GRH_New_edgewise___redArg(v_inst_86_, v_inst_87_, v_u_88_, v_A_89_, v_a_90_, v_a_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg___lam__0(lean_object* v_u_93_, lean_object* v_e_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_97_; lean_object* v_val_98_; lean_object* v___x_99_; 
v___x_97_ = lean_apply_1(v_u_93_, v_e_94_);
v_val_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_98_);
lean_dec_ref(v___x_97_);
v___x_99_ = lean_apply_2(v_val_98_, v___y_95_, v___y_96_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg___lam__1(lean_object* v_Q_x27_100_, lean_object* v_a_101_, lean_object* v_j_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_mathlib_Matrix_transpose___redArg(v_Q_x27_100_, v_a_101_, v_j_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg___lam__2(lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v___f_106_, lean_object* v___x_107_, lean_object* v_a_108_, lean_object* v_j_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lp_GRH_New_edgewise___redArg(v_inst_104_, v_inst_105_, v___f_106_, v___x_107_, v_j_109_, v_a_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_u_117_, lean_object* v_b_118_, lean_object* v_Q_x27_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_toSemiring_122_; lean_object* v___x_123_; lean_object* v_toMul_124_; lean_object* v_toAddCommMonoid_125_; lean_object* v___x_126_; lean_object* v_toZero_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v_toSemiring_122_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref_n(v_toSemiring_122_, 2);
v___x_123_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_122_);
v_toMul_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_toMul_124_);
lean_dec_ref(v___x_123_);
v_toAddCommMonoid_125_ = lean_ctor_get(v_toSemiring_122_, 0);
lean_inc_ref(v_toAddCommMonoid_125_);
v___x_126_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_122_);
v_toZero_127_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_toZero_127_);
lean_dec_ref(v___x_126_);
v___f_128_ = lean_alloc_closure((void*)(lp_GRH_New_pairingMap___redArg___lam__0), 4, 1);
lean_closure_set(v___f_128_, 0, v_u_117_);
v___f_129_ = lean_alloc_closure((void*)(lp_GRH_New_pairingMap___redArg___lam__1), 3, 2);
lean_closure_set(v___f_129_, 0, v_Q_x27_119_);
lean_closure_set(v___f_129_, 1, v_a_120_);
v___x_130_ = lp_mathlib_Multiset_product___redArg(v_inst_113_, v_inst_114_);
v___x_131_ = lp_mathlib_Multiset_product___redArg(v___x_130_, v_inst_115_);
v___x_132_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_132_, 0, lean_box(0));
lean_closure_set(v___x_132_, 1, lean_box(0));
lean_closure_set(v___x_132_, 2, v_inst_116_);
lean_closure_set(v___x_132_, 3, v_toZero_127_);
lean_closure_set(v___x_132_, 4, v_b_118_);
v___f_133_ = lean_alloc_closure((void*)(lp_GRH_New_pairingMap___redArg___lam__2), 6, 5);
lean_closure_set(v___f_133_, 0, v_inst_111_);
lean_closure_set(v___f_133_, 1, v_inst_112_);
lean_closure_set(v___f_133_, 2, v___f_128_);
lean_closure_set(v___f_133_, 3, v___x_132_);
lean_closure_set(v___f_133_, 4, v_a_121_);
v___x_134_ = lp_mathlib_dotProduct___redArg(v___x_131_, v_toMul_124_, v_toAddCommMonoid_125_, v___f_129_, v___f_133_);
lean_dec_ref(v_toAddCommMonoid_125_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap(lean_object* v_O_135_, lean_object* v_H_136_, lean_object* v_Ed_137_, lean_object* v_L_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_E_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_u_147_, lean_object* v_b_148_, lean_object* v_Q_x27_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lp_GRH_New_pairingMap___redArg(v_inst_139_, v_inst_140_, v_inst_141_, v_inst_142_, v_inst_143_, v_inst_146_, v_u_147_, v_b_148_, v_Q_x27_149_, v_a_150_, v_a_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairingMap___boxed(lean_object** _args){
lean_object* v_O_153_ = _args[0];
lean_object* v_H_154_ = _args[1];
lean_object* v_Ed_155_ = _args[2];
lean_object* v_L_156_ = _args[3];
lean_object* v_inst_157_ = _args[4];
lean_object* v_inst_158_ = _args[5];
lean_object* v_inst_159_ = _args[6];
lean_object* v_inst_160_ = _args[7];
lean_object* v_inst_161_ = _args[8];
lean_object* v_E_162_ = _args[9];
lean_object* v_inst_163_ = _args[10];
lean_object* v_inst_164_ = _args[11];
lean_object* v_u_165_ = _args[12];
lean_object* v_b_166_ = _args[13];
lean_object* v_Q_x27_167_ = _args[14];
lean_object* v_a_168_ = _args[15];
lean_object* v_a_169_ = _args[16];
_start:
{
lean_object* v_res_170_; 
v_res_170_ = lp_GRH_New_pairingMap(v_O_153_, v_H_154_, v_Ed_155_, v_L_156_, v_inst_157_, v_inst_158_, v_inst_159_, v_inst_160_, v_inst_161_, v_E_162_, v_inst_163_, v_inst_164_, v_u_165_, v_b_166_, v_Q_x27_167_, v_a_168_, v_a_169_);
lean_dec_ref(v_inst_163_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__0(lean_object* v_u_171_, lean_object* v_e_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_175_; lean_object* v_inv_176_; lean_object* v___x_177_; 
v___x_175_ = lean_apply_1(v_u_171_, v_e_172_);
v_inv_176_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_inv_176_);
lean_dec_ref(v___x_175_);
v___x_177_ = lean_apply_2(v_inv_176_, v___y_173_, v___y_174_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__1(lean_object* v_R_x27_178_, lean_object* v_a_179_, lean_object* v_j_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lp_mathlib_Matrix_transpose___redArg(v_R_x27_178_, v_j_180_, v_a_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__2(lean_object* v_inst_182_, lean_object* v_toZero_183_, lean_object* v_b_x27_184_, lean_object* v___y_185_, lean_object* v_j_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_182_, v_toZero_183_, v_b_x27_184_, v_j_186_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__3(lean_object* v_Av_188_, lean_object* v___y_189_, lean_object* v_j_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_apply_2(v_Av_188_, v___y_189_, v_j_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__4(lean_object* v_inst_192_, lean_object* v_toZero_193_, lean_object* v_b_x27_194_, lean_object* v_Av_195_, lean_object* v_inst_196_, lean_object* v_toMul_197_, lean_object* v_toAddCommMonoid_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v___f_201_ = lean_alloc_closure((void*)(lp_GRH_New_nearInverse___redArg___lam__2), 5, 4);
lean_closure_set(v___f_201_, 0, v_inst_192_);
lean_closure_set(v___f_201_, 1, v_toZero_193_);
lean_closure_set(v___f_201_, 2, v_b_x27_194_);
lean_closure_set(v___f_201_, 3, v___y_200_);
v___f_202_ = lean_alloc_closure((void*)(lp_GRH_New_nearInverse___redArg___lam__3), 3, 2);
lean_closure_set(v___f_202_, 0, v_Av_195_);
lean_closure_set(v___f_202_, 1, v___y_199_);
v___x_203_ = lp_mathlib_dotProduct___redArg(v_inst_196_, v_toMul_197_, v_toAddCommMonoid_198_, v___f_202_, v___f_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__4___boxed(lean_object* v_inst_204_, lean_object* v_toZero_205_, lean_object* v_b_x27_206_, lean_object* v_Av_207_, lean_object* v_inst_208_, lean_object* v_toMul_209_, lean_object* v_toAddCommMonoid_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = lp_GRH_New_nearInverse___redArg___lam__4(v_inst_204_, v_toZero_205_, v_b_x27_206_, v_Av_207_, v_inst_208_, v_toMul_209_, v_toAddCommMonoid_210_, v___y_211_, v___y_212_);
lean_dec_ref(v_toAddCommMonoid_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg___lam__5(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v___f_216_, lean_object* v___f_217_, lean_object* v_a_218_, lean_object* v_j_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lp_GRH_New_edgewise___redArg(v_inst_214_, v_inst_215_, v___f_216_, v___f_217_, v_a_218_, v_j_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___redArg(lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_u_227_, lean_object* v_Av_228_, lean_object* v_b_x27_229_, lean_object* v_R_x27_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_toSemiring_233_; lean_object* v___x_234_; lean_object* v_toMul_235_; lean_object* v_toAddCommMonoid_236_; lean_object* v___x_237_; lean_object* v_toZero_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; 
v_toSemiring_233_ = lean_ctor_get(v_inst_221_, 0);
lean_inc_ref_n(v_toSemiring_233_, 2);
v___x_234_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_233_);
v_toMul_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_n(v_toMul_235_, 2);
lean_dec_ref(v___x_234_);
v_toAddCommMonoid_236_ = lean_ctor_get(v_toSemiring_233_, 0);
lean_inc_ref_n(v_toAddCommMonoid_236_, 2);
v___x_237_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_233_);
v_toZero_238_ = lean_ctor_get(v___x_237_, 1);
lean_inc(v_toZero_238_);
lean_dec_ref(v___x_237_);
v___f_239_ = lean_alloc_closure((void*)(lp_GRH_New_nearInverse___redArg___lam__0), 4, 1);
lean_closure_set(v___f_239_, 0, v_u_227_);
v___f_240_ = lean_alloc_closure((void*)(lp_GRH_New_nearInverse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_240_, 0, v_R_x27_230_);
lean_closure_set(v___f_240_, 1, v_a_232_);
v___x_241_ = lp_mathlib_Multiset_product___redArg(v_inst_223_, v_inst_224_);
lean_inc(v_inst_225_);
v___x_242_ = lp_mathlib_Multiset_product___redArg(v___x_241_, v_inst_225_);
v___f_243_ = lean_alloc_closure((void*)(lp_GRH_New_nearInverse___redArg___lam__4___boxed), 9, 7);
lean_closure_set(v___f_243_, 0, v_inst_226_);
lean_closure_set(v___f_243_, 1, v_toZero_238_);
lean_closure_set(v___f_243_, 2, v_b_x27_229_);
lean_closure_set(v___f_243_, 3, v_Av_228_);
lean_closure_set(v___f_243_, 4, v_inst_225_);
lean_closure_set(v___f_243_, 5, v_toMul_235_);
lean_closure_set(v___f_243_, 6, v_toAddCommMonoid_236_);
v___f_244_ = lean_alloc_closure((void*)(lp_GRH_New_nearInverse___redArg___lam__5), 6, 5);
lean_closure_set(v___f_244_, 0, v_inst_221_);
lean_closure_set(v___f_244_, 1, v_inst_222_);
lean_closure_set(v___f_244_, 2, v___f_239_);
lean_closure_set(v___f_244_, 3, v___f_243_);
lean_closure_set(v___f_244_, 4, v_a_231_);
v___x_245_ = lp_mathlib_dotProduct___redArg(v___x_242_, v_toMul_235_, v_toAddCommMonoid_236_, v___f_244_, v___f_240_);
lean_dec_ref(v_toAddCommMonoid_236_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse(lean_object* v_O_246_, lean_object* v_H_247_, lean_object* v_Ed_248_, lean_object* v_L_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_E_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_u_258_, lean_object* v_Av_259_, lean_object* v_b_x27_260_, lean_object* v_R_x27_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lp_GRH_New_nearInverse___redArg(v_inst_250_, v_inst_251_, v_inst_252_, v_inst_253_, v_inst_254_, v_inst_257_, v_u_258_, v_Av_259_, v_b_x27_260_, v_R_x27_261_, v_a_262_, v_a_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_nearInverse___boxed(lean_object** _args){
lean_object* v_O_265_ = _args[0];
lean_object* v_H_266_ = _args[1];
lean_object* v_Ed_267_ = _args[2];
lean_object* v_L_268_ = _args[3];
lean_object* v_inst_269_ = _args[4];
lean_object* v_inst_270_ = _args[5];
lean_object* v_inst_271_ = _args[6];
lean_object* v_inst_272_ = _args[7];
lean_object* v_inst_273_ = _args[8];
lean_object* v_E_274_ = _args[9];
lean_object* v_inst_275_ = _args[10];
lean_object* v_inst_276_ = _args[11];
lean_object* v_u_277_ = _args[12];
lean_object* v_Av_278_ = _args[13];
lean_object* v_b_x27_279_ = _args[14];
lean_object* v_R_x27_280_ = _args[15];
lean_object* v_a_281_ = _args[16];
lean_object* v_a_282_ = _args[17];
_start:
{
lean_object* v_res_283_; 
v_res_283_ = lp_GRH_New_nearInverse(v_O_265_, v_H_266_, v_Ed_267_, v_L_268_, v_inst_269_, v_inst_270_, v_inst_271_, v_inst_272_, v_inst_273_, v_E_274_, v_inst_275_, v_inst_276_, v_u_277_, v_Av_278_, v_b_x27_279_, v_R_x27_280_, v_a_281_, v_a_282_);
lean_dec_ref(v_inst_275_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision___redArg(lean_object* v_N_284_, lean_object* v_T_285_, lean_object* v_k_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_unsigned_to_nat(5u);
v___x_288_ = lp_GRH_New_FrobeniusCycle_multinomialExponent___redArg(v_N_284_, v_T_285_, v_k_286_);
v___x_289_ = lean_nat_mul(v_N_284_, v___x_288_);
lean_dec(v___x_288_);
v___x_290_ = lean_nat_mul(v___x_287_, v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision___redArg___boxed(lean_object* v_N_291_, lean_object* v_T_292_, lean_object* v_k_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = lp_GRH_New_FrobeniusCycle_congruencePrecision___redArg(v_N_291_, v_T_292_, v_k_293_);
lean_dec(v_k_293_);
lean_dec_ref(v_T_292_);
lean_dec(v_N_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision(lean_object* v_N_295_, lean_object* v_W_296_, lean_object* v_O_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_T_301_, lean_object* v_k_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lp_GRH_New_FrobeniusCycle_congruencePrecision___redArg(v_N_295_, v_T_301_, v_k_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_congruencePrecision___boxed(lean_object* v_N_304_, lean_object* v_W_305_, lean_object* v_O_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_T_310_, lean_object* v_k_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = lp_GRH_New_FrobeniusCycle_congruencePrecision(v_N_304_, v_W_305_, v_O_306_, v_inst_307_, v_inst_308_, v_inst_309_, v_T_310_, v_k_311_);
lean_dec(v_k_311_);
lean_dec_ref(v_T_310_);
lean_dec_ref(v_inst_309_);
lean_dec_ref(v_inst_307_);
lean_dec(v_N_304_);
return v_res_312_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Lattices_Colength(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_AveragingMap(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_DefectCount(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_Depth(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_ElementaryDivisorTheorem(uint8_t builtin) {
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
res = initialize_GRH_New_Reduction_Lattices_Colength(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_AveragingMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_DefectCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_Depth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
