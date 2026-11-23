// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementW public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_, lean_object* v_c_4_, lean_object* v_i_5_, lean_object* v_j_6_){
_start:
{
lean_object* v_toSemiring_7_; lean_object* v___x_8_; lean_object* v_toAdd_9_; lean_object* v___y_11_; uint8_t v___x_15_; uint8_t v___x_16_; uint8_t v___x_17_; lean_object* v___y_19_; 
v_toSemiring_7_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref_n(v_toSemiring_7_, 2);
v___x_8_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_7_);
v_toAdd_9_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_toAdd_9_);
lean_dec_ref(v___x_8_);
v___x_15_ = lean_nat_dec_eq(v_i_5_, v_j_6_);
v___x_16_ = lean_nat_dec_eq(v_j_6_, v_b_3_);
v___x_17_ = lean_nat_dec_eq(v_i_5_, v_a_2_);
if (v___x_15_ == 0)
{
lean_object* v___x_21_; lean_object* v_toZero_22_; 
lean_dec_ref(v_inst_1_);
lean_inc_ref(v_toSemiring_7_);
v___x_21_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_7_);
v_toZero_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_toZero_22_);
lean_dec_ref(v___x_21_);
v___y_19_ = v_toZero_22_;
goto v___jp_18_;
}
else
{
lean_object* v___x_23_; lean_object* v_toAddMonoidWithOne_24_; lean_object* v_toOne_25_; 
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_toAddMonoidWithOne_24_);
lean_dec_ref(v___x_23_);
v_toOne_25_ = lean_ctor_get(v_toAddMonoidWithOne_24_, 2);
lean_inc(v_toOne_25_);
lean_dec_ref(v_toAddMonoidWithOne_24_);
v___y_19_ = v_toOne_25_;
goto v___jp_18_;
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v_toZero_13_; lean_object* v___x_14_; 
v___x_12_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_7_);
v_toZero_13_ = lean_ctor_get(v___x_12_, 1);
lean_inc(v_toZero_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_apply_2(v_toAdd_9_, v___y_11_, v_toZero_13_);
return v___x_14_;
}
v___jp_18_:
{
if (v___x_17_ == 0)
{
lean_dec(v_c_4_);
v___y_11_ = v___y_19_;
goto v___jp_10_;
}
else
{
if (v___x_16_ == 0)
{
lean_dec(v_c_4_);
v___y_11_ = v___y_19_;
goto v___jp_10_;
}
else
{
lean_object* v___x_20_; 
lean_dec_ref(v_toSemiring_7_);
v___x_20_ = lean_apply_2(v_toAdd_9_, v___y_19_, v_c_4_);
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E___redArg___boxed(lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_b_28_, lean_object* v_c_29_, lean_object* v_i_30_, lean_object* v_j_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_UG_P_wlocal__E___redArg(v_inst_26_, v_a_27_, v_b_28_, v_c_29_, v_i_30_, v_j_31_);
lean_dec(v_j_31_);
lean_dec(v_i_30_);
lean_dec(v_b_28_);
lean_dec(v_a_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E(lean_object* v_R_33_, lean_object* v_inst_34_, lean_object* v_r_35_, lean_object* v_a_36_, lean_object* v_b_37_, lean_object* v_c_38_, lean_object* v_i_39_, lean_object* v_j_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Formalism_UG_P_wlocal__E___redArg(v_inst_34_, v_a_36_, v_b_37_, v_c_38_, v_i_39_, v_j_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__E___boxed(lean_object* v_R_42_, lean_object* v_inst_43_, lean_object* v_r_44_, lean_object* v_a_45_, lean_object* v_b_46_, lean_object* v_c_47_, lean_object* v_i_48_, lean_object* v_j_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_UG_P_wlocal__E(v_R_42_, v_inst_43_, v_r_44_, v_a_45_, v_b_46_, v_c_47_, v_i_48_, v_j_49_);
lean_dec(v_j_49_);
lean_dec(v_i_48_);
lean_dec(v_b_46_);
lean_dec(v_a_45_);
lean_dec(v_r_44_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L___redArg(lean_object* v_inst_51_, lean_object* v_k_52_, lean_object* v_c_53_, lean_object* v_i_54_, lean_object* v_j_55_){
_start:
{
lean_object* v_toSemiring_56_; lean_object* v___x_57_; lean_object* v_toAdd_58_; lean_object* v___y_60_; uint8_t v___x_64_; uint8_t v___x_65_; uint8_t v___x_66_; lean_object* v___y_68_; 
v_toSemiring_56_ = lean_ctor_get(v_inst_51_, 0);
lean_inc_ref_n(v_toSemiring_56_, 2);
v___x_57_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_56_);
v_toAdd_58_ = lean_ctor_get(v___x_57_, 1);
lean_inc(v_toAdd_58_);
lean_dec_ref(v___x_57_);
v___x_64_ = lean_nat_dec_eq(v_i_54_, v_j_55_);
v___x_65_ = lean_nat_dec_eq(v_j_55_, v_k_52_);
v___x_66_ = lean_nat_dec_eq(v_i_54_, v_k_52_);
if (v___x_64_ == 0)
{
lean_object* v___x_71_; lean_object* v_toZero_72_; 
lean_dec_ref(v_inst_51_);
lean_inc_ref(v_toSemiring_56_);
v___x_71_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_56_);
v_toZero_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_toZero_72_);
lean_dec_ref(v___x_71_);
v___y_68_ = v_toZero_72_;
goto v___jp_67_;
}
else
{
lean_object* v___x_73_; lean_object* v_toAddMonoidWithOne_74_; lean_object* v_toOne_75_; 
v___x_73_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_51_);
v_toAddMonoidWithOne_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc_ref(v_toAddMonoidWithOne_74_);
lean_dec_ref(v___x_73_);
v_toOne_75_ = lean_ctor_get(v_toAddMonoidWithOne_74_, 2);
lean_inc(v_toOne_75_);
lean_dec_ref(v_toAddMonoidWithOne_74_);
v___y_68_ = v_toOne_75_;
goto v___jp_67_;
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v_toZero_62_; lean_object* v___x_63_; 
v___x_61_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_56_);
v_toZero_62_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_toZero_62_);
lean_dec_ref(v___x_61_);
v___x_63_ = lean_apply_2(v_toAdd_58_, v___y_60_, v_toZero_62_);
return v___x_63_;
}
v___jp_67_:
{
if (v___x_66_ == 0)
{
if (v___x_65_ == 0)
{
lean_dec(v_i_54_);
lean_dec(v_c_53_);
v___y_60_ = v___y_68_;
goto v___jp_59_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec_ref(v_toSemiring_56_);
v___x_69_ = lean_apply_1(v_c_53_, v_i_54_);
v___x_70_ = lean_apply_2(v_toAdd_58_, v___y_68_, v___x_69_);
return v___x_70_;
}
}
else
{
lean_dec(v_i_54_);
lean_dec(v_c_53_);
v___y_60_ = v___y_68_;
goto v___jp_59_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L___redArg___boxed(lean_object* v_inst_76_, lean_object* v_k_77_, lean_object* v_c_78_, lean_object* v_i_79_, lean_object* v_j_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_Formalism_UG_P_wlocal__L___redArg(v_inst_76_, v_k_77_, v_c_78_, v_i_79_, v_j_80_);
lean_dec(v_j_80_);
lean_dec(v_k_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L(lean_object* v_R_82_, lean_object* v_inst_83_, lean_object* v_r_84_, lean_object* v_k_85_, lean_object* v_c_86_, lean_object* v_i_87_, lean_object* v_j_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_tree_Formalism_UG_P_wlocal__L___redArg(v_inst_83_, v_k_85_, v_c_86_, v_i_87_, v_j_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_wlocal__L___boxed(lean_object* v_R_90_, lean_object* v_inst_91_, lean_object* v_r_92_, lean_object* v_k_93_, lean_object* v_c_94_, lean_object* v_i_95_, lean_object* v_j_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_Formalism_UG_P_wlocal__L(v_R_90_, v_inst_91_, v_r_92_, v_k_93_, v_c_94_, v_i_95_, v_j_96_);
lean_dec(v_j_96_);
lean_dec(v_k_93_);
lean_dec(v_r_92_);
return v_res_97_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementW(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
