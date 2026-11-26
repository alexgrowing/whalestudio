// Lean compiler output
// Module: Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations
// Imports: public import Init public meta import Init public import Lib.ClassField.Places.DecompositionCompletion public import Lib.General.LinearAlgebra.Eigenvalues public import Lib.General.LinearAlgebra.MatrixNormBounds public import Lib.General.NumberTheory.CoefficientRings public import Lib.PadicComparison.Descent.TestCategory
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_single(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_single___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_blockDiagonal_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AlgHom_toMonoidHom_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalAlgHom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalAlgHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalAlgHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalAlgHom___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v_toSemiring_3_; lean_object* v___x_4_; lean_object* v_toZero_5_; lean_object* v___x_6_; lean_object* v___f_7_; 
v_toSemiring_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_3_);
lean_dec_ref(v_inst_1_);
v___x_4_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_3_);
v_toZero_5_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_toZero_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_blockDiagonal_x27), 9, 6);
lean_closure_set(v___x_6_, 0, lean_box(0));
lean_closure_set(v___x_6_, 1, lean_box(0));
lean_closure_set(v___x_6_, 2, lean_box(0));
lean_closure_set(v___x_6_, 3, lean_box(0));
lean_closure_set(v___x_6_, 4, v_inst_2_);
lean_closure_set(v___x_6_, 5, v_toZero_5_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_AlgHom_toMonoidHom_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_7_, 0, v___x_6_);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalAlgHom(lean_object* v_R_8_, lean_object* v_o_9_, lean_object* v_m_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_GRH_New_blockDiagonalAlgHom___redArg(v_inst_11_, v_inst_12_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalAlgHom___boxed(lean_object* v_R_17_, lean_object* v_o_18_, lean_object* v_m_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_blockDiagonalAlgHom(v_R_17_, v_o_18_, v_m_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_inst_24_);
lean_dec_ref(v_inst_24_);
lean_dec(v_inst_23_);
lean_dec(v_inst_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit___redArg___lam__0(lean_object* v_toZero_26_, lean_object* v_i_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_inc(v_toZero_26_);
return v_toZero_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit___redArg___lam__0___boxed(lean_object* v_toZero_30_, lean_object* v_i_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_piMatrixUnit___redArg___lam__0(v_toZero_30_, v_i_31_, v___y_32_, v___y_33_);
lean_dec(v___y_33_);
lean_dec(v___y_32_);
lean_dec(v_i_31_);
lean_dec(v_toZero_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit___redArg(lean_object* v_inst_35_, lean_object* v_m_36_, lean_object* v_d_37_, lean_object* v_i_38_, lean_object* v_a_39_, lean_object* v_b_40_, lean_object* v_j_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; lean_object* v_toCommSemiring_45_; lean_object* v___x_46_; lean_object* v_toZero_47_; lean_object* v___x_48_; lean_object* v_toRing_49_; lean_object* v___x_50_; lean_object* v_toAddMonoidWithOne_51_; lean_object* v_toOne_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_112__overap_58_; lean_object* v___x_59_; 
v___x_44_ = lp_mathlib_Field_toSemifield___redArg(v_inst_35_);
v_toCommSemiring_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_toCommSemiring_45_);
lean_dec_ref(v___x_44_);
v___x_46_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_45_);
v_toZero_47_ = lean_ctor_get(v___x_46_, 1);
lean_inc_n(v_toZero_47_, 2);
lean_dec_ref(v___x_46_);
v___x_48_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_35_);
v_toRing_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_toRing_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_49_);
v_toAddMonoidWithOne_51_ = lean_ctor_get(v___x_50_, 1);
lean_inc_ref(v_toAddMonoidWithOne_51_);
lean_dec_ref(v___x_50_);
v_toOne_52_ = lean_ctor_get(v_toAddMonoidWithOne_51_, 2);
lean_inc(v_toOne_52_);
lean_dec_ref(v_toAddMonoidWithOne_51_);
v___f_53_ = lean_alloc_closure((void*)(lp_GRH_New_piMatrixUnit___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_53_, 0, v_toZero_47_);
v___x_54_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_54_, 0, v_m_36_);
lean_inc(v_i_38_);
v___x_55_ = lean_apply_1(v_d_37_, v_i_38_);
v___x_56_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_56_, 0, v___x_55_);
lean_inc_ref(v___x_56_);
v___x_57_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_single), 11, 9);
lean_closure_set(v___x_57_, 0, lean_box(0));
lean_closure_set(v___x_57_, 1, lean_box(0));
lean_closure_set(v___x_57_, 2, lean_box(0));
lean_closure_set(v___x_57_, 3, v___x_56_);
lean_closure_set(v___x_57_, 4, v___x_56_);
lean_closure_set(v___x_57_, 5, v_toZero_47_);
lean_closure_set(v___x_57_, 6, v_a_39_);
lean_closure_set(v___x_57_, 7, v_b_40_);
lean_closure_set(v___x_57_, 8, v_toOne_52_);
v___x_112__overap_58_ = lp_mathlib_Pi_single___redArg(v___f_53_, v___x_54_, v_i_38_, v___x_57_, v_j_41_);
lean_dec_ref(v___x_57_);
v___x_59_ = lean_apply_2(v___x_112__overap_58_, v_a_42_, v_a_43_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_piMatrixUnit(lean_object* v_k_60_, lean_object* v_inst_61_, lean_object* v_m_62_, lean_object* v_d_63_, lean_object* v_inst_64_, lean_object* v_i_65_, lean_object* v_a_66_, lean_object* v_b_67_, lean_object* v_j_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; lean_object* v_toCommSemiring_72_; lean_object* v___x_73_; lean_object* v_toZero_74_; lean_object* v___x_75_; lean_object* v_toRing_76_; lean_object* v___x_77_; lean_object* v_toAddMonoidWithOne_78_; lean_object* v_toOne_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_137__overap_85_; lean_object* v___x_86_; 
v___x_71_ = lp_mathlib_Field_toSemifield___redArg(v_inst_61_);
v_toCommSemiring_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_toCommSemiring_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_72_);
v_toZero_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc_n(v_toZero_74_, 2);
lean_dec_ref(v___x_73_);
v___x_75_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_61_);
v_toRing_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_toRing_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_76_);
v_toAddMonoidWithOne_78_ = lean_ctor_get(v___x_77_, 1);
lean_inc_ref(v_toAddMonoidWithOne_78_);
lean_dec_ref(v___x_77_);
v_toOne_79_ = lean_ctor_get(v_toAddMonoidWithOne_78_, 2);
lean_inc(v_toOne_79_);
lean_dec_ref(v_toAddMonoidWithOne_78_);
v___f_80_ = lean_alloc_closure((void*)(lp_GRH_New_piMatrixUnit___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_80_, 0, v_toZero_74_);
v___x_81_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_81_, 0, v_m_62_);
lean_inc(v_i_65_);
v___x_82_ = lean_apply_1(v_d_63_, v_i_65_);
v___x_83_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_83_, 0, v___x_82_);
lean_inc_ref(v___x_83_);
v___x_84_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_single), 11, 9);
lean_closure_set(v___x_84_, 0, lean_box(0));
lean_closure_set(v___x_84_, 1, lean_box(0));
lean_closure_set(v___x_84_, 2, lean_box(0));
lean_closure_set(v___x_84_, 3, v___x_83_);
lean_closure_set(v___x_84_, 4, v___x_83_);
lean_closure_set(v___x_84_, 5, v_toZero_74_);
lean_closure_set(v___x_84_, 6, v_a_66_);
lean_closure_set(v___x_84_, 7, v_b_67_);
lean_closure_set(v___x_84_, 8, v_toOne_79_);
v___x_137__overap_85_ = lp_mathlib_Pi_single___redArg(v___f_80_, v___x_81_, v_i_65_, v___x_84_, v_j_68_);
lean_dec_ref(v___x_84_);
v___x_86_ = lean_apply_2(v___x_137__overap_85_, v_a_69_, v_a_70_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__0(lean_object* v_f_87_, lean_object* v___x_88_, lean_object* v___y_89_, lean_object* v_j_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_apply_3(v_f_87_, v___x_88_, v___y_89_, v_j_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__1(lean_object* v_U_92_, lean_object* v_i_93_, lean_object* v_j_94_, lean_object* v_j_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_apply_3(v_U_92_, v_i_93_, v_j_95_, v_j_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__2(lean_object* v_U_97_, lean_object* v_i_98_, lean_object* v_inst_99_, lean_object* v_toMul_100_, lean_object* v_toAddCommMonoid_101_, lean_object* v___f_102_, lean_object* v_j_103_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; 
v___f_104_ = lean_alloc_closure((void*)(lp_GRH_New_intertwiner___redArg___lam__1), 4, 3);
lean_closure_set(v___f_104_, 0, v_U_97_);
lean_closure_set(v___f_104_, 1, v_i_98_);
lean_closure_set(v___f_104_, 2, v_j_103_);
v___x_105_ = lp_mathlib_dotProduct___redArg(v_inst_99_, v_toMul_100_, v_toAddCommMonoid_101_, v___f_102_, v___f_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__2___boxed(lean_object* v_U_106_, lean_object* v_i_107_, lean_object* v_inst_108_, lean_object* v_toMul_109_, lean_object* v_toAddCommMonoid_110_, lean_object* v___f_111_, lean_object* v_j_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = lp_GRH_New_intertwiner___redArg___lam__2(v_U_106_, v_i_107_, v_inst_108_, v_toMul_109_, v_toAddCommMonoid_110_, v___f_111_, v_j_112_);
lean_dec_ref(v_toAddCommMonoid_110_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__3(lean_object* v_f_x27_114_, lean_object* v___x_115_, lean_object* v___y_116_, lean_object* v_j_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_apply_3(v_f_x27_114_, v___x_115_, v_j_117_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__4(lean_object* v___x_119_, lean_object* v_inst_120_, lean_object* v_m_121_, lean_object* v_d_122_, lean_object* v_i_123_, lean_object* v_f_124_, lean_object* v_U_125_, lean_object* v_inst_126_, lean_object* v_toMul_127_, lean_object* v_toAddCommMonoid_128_, lean_object* v_f_x27_129_, lean_object* v_inst_130_, lean_object* v_a_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___x_141_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_nat_mod(v___x_134_, v___x_119_);
lean_inc(v___x_135_);
lean_inc(v_a_131_);
lean_inc_n(v_i_123_, 2);
lean_inc_ref(v_d_122_);
lean_inc(v_m_121_);
lean_inc_ref(v_inst_120_);
v___x_136_ = lean_alloc_closure((void*)(lp_GRH_New_piMatrixUnit), 11, 8);
lean_closure_set(v___x_136_, 0, lean_box(0));
lean_closure_set(v___x_136_, 1, v_inst_120_);
lean_closure_set(v___x_136_, 2, v_m_121_);
lean_closure_set(v___x_136_, 3, v_d_122_);
lean_closure_set(v___x_136_, 4, lean_box(0));
lean_closure_set(v___x_136_, 5, v_i_123_);
lean_closure_set(v___x_136_, 6, v_a_131_);
lean_closure_set(v___x_136_, 7, v___x_135_);
v___f_137_ = lean_alloc_closure((void*)(lp_GRH_New_intertwiner___redArg___lam__0), 4, 3);
lean_closure_set(v___f_137_, 0, v_f_124_);
lean_closure_set(v___f_137_, 1, v___x_136_);
lean_closure_set(v___f_137_, 2, v___y_132_);
lean_inc_ref(v_toAddCommMonoid_128_);
lean_inc(v_toMul_127_);
v___f_138_ = lean_alloc_closure((void*)(lp_GRH_New_intertwiner___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_138_, 0, v_U_125_);
lean_closure_set(v___f_138_, 1, v_i_123_);
lean_closure_set(v___f_138_, 2, v_inst_126_);
lean_closure_set(v___f_138_, 3, v_toMul_127_);
lean_closure_set(v___f_138_, 4, v_toAddCommMonoid_128_);
lean_closure_set(v___f_138_, 5, v___f_137_);
v___x_139_ = lean_alloc_closure((void*)(lp_GRH_New_piMatrixUnit), 11, 8);
lean_closure_set(v___x_139_, 0, lean_box(0));
lean_closure_set(v___x_139_, 1, v_inst_120_);
lean_closure_set(v___x_139_, 2, v_m_121_);
lean_closure_set(v___x_139_, 3, v_d_122_);
lean_closure_set(v___x_139_, 4, lean_box(0));
lean_closure_set(v___x_139_, 5, v_i_123_);
lean_closure_set(v___x_139_, 6, v___x_135_);
lean_closure_set(v___x_139_, 7, v_a_131_);
v___f_140_ = lean_alloc_closure((void*)(lp_GRH_New_intertwiner___redArg___lam__3), 4, 3);
lean_closure_set(v___f_140_, 0, v_f_x27_129_);
lean_closure_set(v___f_140_, 1, v___x_139_);
lean_closure_set(v___f_140_, 2, v___y_133_);
v___x_141_ = lp_mathlib_dotProduct___redArg(v_inst_130_, v_toMul_127_, v_toAddCommMonoid_128_, v___f_138_, v___f_140_);
lean_dec_ref(v_toAddCommMonoid_128_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__4___boxed(lean_object* v___x_142_, lean_object* v_inst_143_, lean_object* v_m_144_, lean_object* v_d_145_, lean_object* v_i_146_, lean_object* v_f_147_, lean_object* v_U_148_, lean_object* v_inst_149_, lean_object* v_toMul_150_, lean_object* v_toAddCommMonoid_151_, lean_object* v_f_x27_152_, lean_object* v_inst_153_, lean_object* v_a_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_GRH_New_intertwiner___redArg___lam__4(v___x_142_, v_inst_143_, v_m_144_, v_d_145_, v_i_146_, v_f_147_, v_U_148_, v_inst_149_, v_toMul_150_, v_toAddCommMonoid_151_, v_f_x27_152_, v_inst_153_, v_a_154_, v___y_155_, v___y_156_);
lean_dec(v___x_142_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__5(lean_object* v_d_158_, lean_object* v_inst_159_, lean_object* v_m_160_, lean_object* v_f_161_, lean_object* v_U_162_, lean_object* v_inst_163_, lean_object* v_toMul_164_, lean_object* v_toAddCommMonoid_165_, lean_object* v_f_x27_166_, lean_object* v_inst_167_, lean_object* v___x_168_, lean_object* v_i_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_193__overap_175_; lean_object* v___x_176_; 
lean_inc_ref(v_d_158_);
lean_inc(v_i_169_);
v___x_172_ = lean_apply_1(v_d_158_, v_i_169_);
lean_inc(v___x_172_);
v___f_173_ = lean_alloc_closure((void*)(lp_GRH_New_intertwiner___redArg___lam__4___boxed), 15, 12);
lean_closure_set(v___f_173_, 0, v___x_172_);
lean_closure_set(v___f_173_, 1, v_inst_159_);
lean_closure_set(v___f_173_, 2, v_m_160_);
lean_closure_set(v___f_173_, 3, v_d_158_);
lean_closure_set(v___f_173_, 4, v_i_169_);
lean_closure_set(v___f_173_, 5, v_f_161_);
lean_closure_set(v___f_173_, 6, v_U_162_);
lean_closure_set(v___f_173_, 7, v_inst_163_);
lean_closure_set(v___f_173_, 8, v_toMul_164_);
lean_closure_set(v___f_173_, 9, v_toAddCommMonoid_165_);
lean_closure_set(v___f_173_, 10, v_f_x27_166_);
lean_closure_set(v___f_173_, 11, v_inst_167_);
v___x_174_ = l_List_finRange(v___x_172_);
v___x_193__overap_175_ = lp_mathlib_Finset_sum___redArg(v___x_168_, v___x_174_, v___f_173_);
v___x_176_ = lean_apply_2(v___x_193__overap_175_, v___y_170_, v___y_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg___lam__5___boxed(lean_object* v_d_177_, lean_object* v_inst_178_, lean_object* v_m_179_, lean_object* v_f_180_, lean_object* v_U_181_, lean_object* v_inst_182_, lean_object* v_toMul_183_, lean_object* v_toAddCommMonoid_184_, lean_object* v_f_x27_185_, lean_object* v_inst_186_, lean_object* v___x_187_, lean_object* v_i_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_GRH_New_intertwiner___redArg___lam__5(v_d_177_, v_inst_178_, v_m_179_, v_f_180_, v_U_181_, v_inst_182_, v_toMul_183_, v_toAddCommMonoid_184_, v_f_x27_185_, v_inst_186_, v___x_187_, v_i_188_, v___y_189_, v___y_190_);
lean_dec_ref(v___x_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_m_195_, lean_object* v_d_196_, lean_object* v_f_197_, lean_object* v_f_x27_198_, lean_object* v_U_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; lean_object* v_toCommSemiring_203_; lean_object* v_toAddCommMonoid_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_toMul_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___x_145__overap_210_; lean_object* v___x_211_; 
v___x_202_ = lp_mathlib_Field_toSemifield___redArg(v_inst_192_);
v_toCommSemiring_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_toCommSemiring_203_);
lean_dec_ref(v___x_202_);
v_toAddCommMonoid_204_ = lean_ctor_get(v_toCommSemiring_203_, 0);
lean_inc_ref_n(v_toAddCommMonoid_204_, 2);
v___x_205_ = lp_mathlib_Matrix_addMonoid___redArg(v_toAddCommMonoid_204_);
v___x_206_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_203_);
v_toMul_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_toMul_207_);
lean_dec_ref(v___x_206_);
lean_inc(v_m_195_);
v___x_208_ = l_List_finRange(v_m_195_);
lean_inc_ref(v___x_205_);
v___f_209_ = lean_alloc_closure((void*)(lp_GRH_New_intertwiner___redArg___lam__5___boxed), 14, 11);
lean_closure_set(v___f_209_, 0, v_d_196_);
lean_closure_set(v___f_209_, 1, v_inst_192_);
lean_closure_set(v___f_209_, 2, v_m_195_);
lean_closure_set(v___f_209_, 3, v_f_197_);
lean_closure_set(v___f_209_, 4, v_U_199_);
lean_closure_set(v___f_209_, 5, v_inst_194_);
lean_closure_set(v___f_209_, 6, v_toMul_207_);
lean_closure_set(v___f_209_, 7, v_toAddCommMonoid_204_);
lean_closure_set(v___f_209_, 8, v_f_x27_198_);
lean_closure_set(v___f_209_, 9, v_inst_193_);
lean_closure_set(v___f_209_, 10, v___x_205_);
v___x_145__overap_210_ = lp_mathlib_Finset_sum___redArg(v___x_205_, v___x_208_, v___f_209_);
lean_dec_ref(v___x_205_);
v___x_211_ = lean_apply_2(v___x_145__overap_210_, v_a_200_, v_a_201_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner(lean_object* v_k_212_, lean_object* v_n_213_, lean_object* v_N_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_m_220_, lean_object* v_d_221_, lean_object* v_inst_222_, lean_object* v_f_223_, lean_object* v_f_x27_224_, lean_object* v_U_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lp_GRH_New_intertwiner___redArg(v_inst_215_, v_inst_216_, v_inst_218_, v_m_220_, v_d_221_, v_f_223_, v_f_x27_224_, v_U_225_, v_a_226_, v_a_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intertwiner___boxed(lean_object* v_k_229_, lean_object* v_n_230_, lean_object* v_N_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_m_237_, lean_object* v_d_238_, lean_object* v_inst_239_, lean_object* v_f_240_, lean_object* v_f_x27_241_, lean_object* v_U_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_GRH_New_intertwiner(v_k_229_, v_n_230_, v_N_231_, v_inst_232_, v_inst_233_, v_inst_234_, v_inst_235_, v_inst_236_, v_m_237_, v_d_238_, v_inst_239_, v_f_240_, v_f_x27_241_, v_U_242_, v_a_243_, v_a_244_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_234_);
return v_res_245_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_DecompositionCompletion(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_CoefficientRings(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_Descent_TestCategory(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_Pseudocharacter_SemisimpleRepresentations(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Places_DecompositionCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_CoefficientRings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_Descent_TestCategory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
