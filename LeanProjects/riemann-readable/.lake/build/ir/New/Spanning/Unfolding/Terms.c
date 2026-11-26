// Lean compiler output
// Module: New.Spanning.Unfolding.Terms
// Imports: public import Init public meta import Init public import New.Spanning.RemainingTerms.Box public import New.Spanning.RemainingTerms.SiegelLemma public import New.Spanning.Unfolding.BesselLevelStructure
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_GRH_New_Filling_ratMiddle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_neg___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toRows_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Shape_Form_splitGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zRowBlockDiagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zRowBlockDiagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zRowBlockDiagonal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_commonLink___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_commonLink___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_commonLink(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_commonLink___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_ratGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_ratGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkForm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkForm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zRowBlockDiagonal___redArg(lean_object* v_inst_1_, lean_object* v_T_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v_toSemiring_5_; lean_object* v___x_6_; lean_object* v_toZero_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_toSemiring_5_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v_inst_1_);
v___x_6_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_5_);
v_toZero_7_ = lean_ctor_get(v___x_6_, 1);
lean_inc(v_toZero_7_);
lean_dec_ref(v___x_6_);
v___x_8_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toRows_u2082), 7, 5);
lean_closure_set(v___x_8_, 0, lean_box(0));
lean_closure_set(v___x_8_, 1, lean_box(0));
lean_closure_set(v___x_8_, 2, lean_box(0));
lean_closure_set(v___x_8_, 3, lean_box(0));
lean_closure_set(v___x_8_, 4, v_T_2_);
v___x_9_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_9_, 0, lean_box(0));
lean_closure_set(v___x_9_, 1, lean_box(0));
lean_closure_set(v___x_9_, 2, lean_box(0));
lean_closure_set(v___x_9_, 3, v_toZero_7_);
lean_inc_ref(v___x_9_);
lean_inc_ref(v___x_8_);
v___x_10_ = lp_mathlib_Matrix_fromBlocks___redArg(v___x_8_, v___x_9_, v___x_9_, v___x_8_, v_a_3_, v_a_4_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zRowBlockDiagonal(lean_object* v_R_11_, lean_object* v_inst_12_, lean_object* v_00_U0001d530_13_, lean_object* v_T_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_toSemiring_17_; lean_object* v___x_18_; lean_object* v_toZero_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_toSemiring_17_ = lean_ctor_get(v_inst_12_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v_inst_12_);
v___x_18_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_17_);
v_toZero_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_toZero_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_toRows_u2082), 7, 5);
lean_closure_set(v___x_20_, 0, lean_box(0));
lean_closure_set(v___x_20_, 1, lean_box(0));
lean_closure_set(v___x_20_, 2, lean_box(0));
lean_closure_set(v___x_20_, 3, lean_box(0));
lean_closure_set(v___x_20_, 4, v_T_14_);
v___x_21_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_21_, 0, lean_box(0));
lean_closure_set(v___x_21_, 1, lean_box(0));
lean_closure_set(v___x_21_, 2, lean_box(0));
lean_closure_set(v___x_21_, 3, v_toZero_19_);
lean_inc_ref(v___x_21_);
lean_inc_ref(v___x_20_);
v___x_22_ = lp_mathlib_Matrix_fromBlocks___redArg(v___x_20_, v___x_21_, v___x_21_, v___x_20_, v_a_15_, v_a_16_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zRowBlockDiagonal___boxed(lean_object* v_R_23_, lean_object* v_inst_24_, lean_object* v_00_U0001d530_25_, lean_object* v_T_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_GRH_New_Filling_zRowBlockDiagonal(v_R_23_, v_inst_24_, v_00_U0001d530_25_, v_T_26_, v_a_27_, v_a_28_);
lean_dec_ref(v_00_U0001d530_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_commonLink___redArg(){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_commonLink___redArg___boxed(lean_object* v___dummy_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_commonLink___redArg();
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_commonLink(lean_object* v_R_34_, lean_object* v_inst_35_, lean_object* v_00_U0001d530_36_, lean_object* v_inst_37_, lean_object* v_T_38_, lean_object* v_00_u03b3_39_, lean_object* v_00_u03b3_x27_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_commonLink___boxed(lean_object* v_R_42_, lean_object* v_inst_43_, lean_object* v_00_U0001d530_44_, lean_object* v_inst_45_, lean_object* v_T_46_, lean_object* v_00_u03b3_47_, lean_object* v_00_u03b3_x27_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH_New_commonLink(v_R_42_, v_inst_43_, v_00_U0001d530_44_, v_inst_45_, v_T_46_, v_00_u03b3_47_, v_00_u03b3_x27_48_);
lean_dec_ref(v_00_u03b3_x27_48_);
lean_dec_ref(v_00_u03b3_47_);
lean_dec(v_T_46_);
lean_dec(v_inst_45_);
lean_dec_ref(v_00_U0001d530_44_);
lean_dec_ref(v_inst_43_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_ratGram___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_00_U0001d530_52_, lean_object* v_S_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_toCommRing_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_toCommRing_56_ = lean_ctor_get(v_inst_50_, 0);
lean_inc_ref_n(v_toCommRing_56_, 2);
lean_inc_ref(v_00_U0001d530_52_);
v___x_57_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_ratMiddle___boxed), 9, 7);
lean_closure_set(v___x_57_, 0, lean_box(0));
lean_closure_set(v___x_57_, 1, v_inst_50_);
lean_closure_set(v___x_57_, 2, v_inst_51_);
lean_closure_set(v___x_57_, 3, v_00_U0001d530_52_);
lean_closure_set(v___x_57_, 4, v_S_53_);
lean_closure_set(v___x_57_, 5, lean_box(0));
lean_closure_set(v___x_57_, 6, v_toCommRing_56_);
v___x_58_ = lp_GRH_New_Shape_Form_splitGram___redArg(v_toCommRing_56_, v_00_U0001d530_52_, v___x_57_, v_a_54_, v_a_55_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_ratGram(lean_object* v_E_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_00_U0001d530_62_, lean_object* v_S_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_toCommRing_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_toCommRing_66_ = lean_ctor_get(v_inst_60_, 0);
lean_inc_ref_n(v_toCommRing_66_, 2);
lean_inc_ref(v_00_U0001d530_62_);
v___x_67_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_ratMiddle___boxed), 9, 7);
lean_closure_set(v___x_67_, 0, lean_box(0));
lean_closure_set(v___x_67_, 1, v_inst_60_);
lean_closure_set(v___x_67_, 2, v_inst_61_);
lean_closure_set(v___x_67_, 3, v_00_U0001d530_62_);
lean_closure_set(v___x_67_, 4, v_S_63_);
lean_closure_set(v___x_67_, 5, lean_box(0));
lean_closure_set(v___x_67_, 6, v_toCommRing_66_);
v___x_68_ = lp_GRH_New_Shape_Form_splitGram___redArg(v_toCommRing_66_, v_00_U0001d530_62_, v___x_67_, v_a_64_, v_a_65_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkForm___redArg(lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_00_U0001d530_71_, lean_object* v_S_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_toCommRing_75_; lean_object* v___x_76_; lean_object* v_toCommSemiring_77_; lean_object* v___x_78_; lean_object* v_toZero_79_; lean_object* v___x_80_; lean_object* v_toRing_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_toNeg_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_toCommRing_75_ = lean_ctor_get(v_inst_69_, 0);
lean_inc_ref(v_toCommRing_75_);
v___x_76_ = lp_mathlib_Field_toSemifield___redArg(v_inst_69_);
v_toCommSemiring_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_toCommSemiring_77_);
lean_dec_ref(v___x_76_);
v___x_78_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_77_);
v_toZero_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_toZero_79_);
lean_dec_ref(v___x_78_);
lean_inc_ref(v_inst_69_);
v___x_80_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_69_);
v_toRing_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc_ref(v_toRing_81_);
lean_dec_ref(v___x_80_);
v___x_82_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_81_);
lean_dec_ref(v_toRing_81_);
v___x_83_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_82_);
lean_dec_ref(v___x_82_);
v_toNeg_84_ = lean_ctor_get(v___x_83_, 1);
lean_inc(v_toNeg_84_);
lean_dec_ref(v___x_83_);
v___x_85_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_ratMiddle___boxed), 9, 7);
lean_closure_set(v___x_85_, 0, lean_box(0));
lean_closure_set(v___x_85_, 1, v_inst_69_);
lean_closure_set(v___x_85_, 2, v_inst_70_);
lean_closure_set(v___x_85_, 3, v_00_U0001d530_71_);
lean_closure_set(v___x_85_, 4, v_S_72_);
lean_closure_set(v___x_85_, 5, lean_box(0));
lean_closure_set(v___x_85_, 6, v_toCommRing_75_);
v___x_86_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_86_, 0, lean_box(0));
lean_closure_set(v___x_86_, 1, lean_box(0));
lean_closure_set(v___x_86_, 2, lean_box(0));
lean_closure_set(v___x_86_, 3, v_toZero_79_);
lean_inc_ref(v___x_85_);
v___x_87_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_neg___aux__1), 7, 5);
lean_closure_set(v___x_87_, 0, lean_box(0));
lean_closure_set(v___x_87_, 1, lean_box(0));
lean_closure_set(v___x_87_, 2, lean_box(0));
lean_closure_set(v___x_87_, 3, v_toNeg_84_);
lean_closure_set(v___x_87_, 4, v___x_85_);
lean_inc_ref(v___x_86_);
v___x_88_ = lp_mathlib_Matrix_fromBlocks___redArg(v___x_85_, v___x_86_, v___x_86_, v___x_87_, v_a_73_, v_a_74_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkForm(lean_object* v_E_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_00_U0001d530_92_, lean_object* v_S_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_toCommRing_96_; lean_object* v___x_97_; lean_object* v_toCommSemiring_98_; lean_object* v___x_99_; lean_object* v_toZero_100_; lean_object* v___x_101_; lean_object* v_toRing_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_toNeg_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_toCommRing_96_ = lean_ctor_get(v_inst_90_, 0);
lean_inc_ref(v_toCommRing_96_);
v___x_97_ = lp_mathlib_Field_toSemifield___redArg(v_inst_90_);
v_toCommSemiring_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_toCommSemiring_98_);
lean_dec_ref(v___x_97_);
v___x_99_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_98_);
v_toZero_100_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_toZero_100_);
lean_dec_ref(v___x_99_);
lean_inc_ref(v_inst_90_);
v___x_101_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_90_);
v_toRing_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_toRing_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_102_);
lean_dec_ref(v_toRing_102_);
v___x_104_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_103_);
lean_dec_ref(v___x_103_);
v_toNeg_105_ = lean_ctor_get(v___x_104_, 1);
lean_inc(v_toNeg_105_);
lean_dec_ref(v___x_104_);
v___x_106_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_ratMiddle___boxed), 9, 7);
lean_closure_set(v___x_106_, 0, lean_box(0));
lean_closure_set(v___x_106_, 1, v_inst_90_);
lean_closure_set(v___x_106_, 2, v_inst_91_);
lean_closure_set(v___x_106_, 3, v_00_U0001d530_92_);
lean_closure_set(v___x_106_, 4, v_S_93_);
lean_closure_set(v___x_106_, 5, lean_box(0));
lean_closure_set(v___x_106_, 6, v_toCommRing_96_);
v___x_107_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_107_, 0, lean_box(0));
lean_closure_set(v___x_107_, 1, lean_box(0));
lean_closure_set(v___x_107_, 2, lean_box(0));
lean_closure_set(v___x_107_, 3, v_toZero_100_);
lean_inc_ref(v___x_106_);
v___x_108_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_neg___aux__1), 7, 5);
lean_closure_set(v___x_108_, 0, lean_box(0));
lean_closure_set(v___x_108_, 1, lean_box(0));
lean_closure_set(v___x_108_, 2, lean_box(0));
lean_closure_set(v___x_108_, 3, v_toNeg_105_);
lean_closure_set(v___x_108_, 4, v___x_106_);
lean_inc_ref(v___x_107_);
v___x_109_ = lp_mathlib_Matrix_fromBlocks___redArg(v___x_106_, v___x_107_, v___x_107_, v___x_108_, v_a_94_, v_a_95_);
return v___x_109_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_Box(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_SiegelLemma(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_BesselLevelStructure(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_Terms(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_RemainingTerms_Box(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_RemainingTerms_SiegelLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_BesselLevelStructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
