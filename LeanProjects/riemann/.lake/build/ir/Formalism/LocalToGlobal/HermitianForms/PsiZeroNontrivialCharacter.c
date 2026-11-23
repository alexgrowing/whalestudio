// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkOf(lean_object* v_a_1_, lean_object* v_t_2_, lean_object* v_x_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_x_3_, v_a_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_nat_sub(v_x_3_, v_a_1_);
v___x_6_ = lean_nat_div(v___x_5_, v_t_2_);
lean_dec(v___x_5_);
v___x_7_ = lean_nat_add(v_a_1_, v___x_6_);
lean_dec(v___x_6_);
return v___x_7_;
}
else
{
lean_inc(v_x_3_);
return v_x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkOf___boxed(lean_object* v_a_8_, lean_object* v_t_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_L2_Forms_blkOf(v_a_8_, v_t_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_t_9_);
lean_dec(v_a_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN___redArg(lean_object* v_inst_12_, lean_object* v_n_13_, lean_object* v_M_14_, lean_object* v_x_15_, lean_object* v_y_16_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_lt(v_x_15_, v_n_13_);
if (v___x_23_ == 0)
{
lean_dec(v_y_16_);
lean_dec(v_x_15_);
lean_dec(v_M_14_);
goto v___jp_17_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_nat_dec_lt(v_y_16_, v_n_13_);
if (v___x_24_ == 0)
{
lean_dec(v_y_16_);
lean_dec(v_x_15_);
lean_dec(v_M_14_);
goto v___jp_17_;
}
else
{
lean_object* v___x_25_; 
v___x_25_ = lean_apply_2(v_M_14_, v_x_15_, v_y_16_);
return v___x_25_;
}
}
v___jp_17_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toSemiring_20_; lean_object* v___x_21_; lean_object* v_toZero_22_; 
v___x_18_ = lp_mathlib_Field_toSemifield___redArg(v_inst_12_);
v___x_19_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_18_);
v_toSemiring_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_toSemiring_20_);
lean_dec_ref(v___x_19_);
v___x_21_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_20_);
v_toZero_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_toZero_22_);
lean_dec_ref(v___x_21_);
return v_toZero_22_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN___redArg___boxed(lean_object* v_inst_26_, lean_object* v_n_27_, lean_object* v_M_28_, lean_object* v_x_29_, lean_object* v_y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_Forms_entN___redArg(v_inst_26_, v_n_27_, v_M_28_, v_x_29_, v_y_30_);
lean_dec(v_n_27_);
lean_dec_ref(v_inst_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN(lean_object* v_k_32_, lean_object* v_inst_33_, lean_object* v_n_34_, lean_object* v_M_35_, lean_object* v_x_36_, lean_object* v_y_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_tree_Formalism_L2_Forms_entN___redArg(v_inst_33_, v_n_34_, v_M_35_, v_x_36_, v_y_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_entN___boxed(lean_object* v_k_39_, lean_object* v_inst_40_, lean_object* v_n_41_, lean_object* v_M_42_, lean_object* v_x_43_, lean_object* v_y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_L2_Forms_entN(v_k_39_, v_inst_40_, v_n_41_, v_M_42_, v_x_43_, v_y_44_);
lean_dec(v_n_41_);
lean_dec_ref(v_inst_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat___redArg(lean_object* v_inst_46_, lean_object* v_n_47_, lean_object* v_a_48_, lean_object* v_t_49_, lean_object* v_i_50_, lean_object* v_M_51_, lean_object* v_s_52_, lean_object* v_s_x27_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = lean_nat_mul(v_i_50_, v_t_49_);
v___x_55_ = lean_nat_add(v_a_48_, v___x_54_);
lean_dec(v___x_54_);
v___x_56_ = lean_nat_add(v___x_55_, v_s_52_);
v___x_57_ = lean_nat_add(v___x_55_, v_s_x27_53_);
lean_dec(v___x_55_);
v___x_58_ = lp_tree_Formalism_L2_Forms_entN___redArg(v_inst_46_, v_n_47_, v_M_51_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat___redArg___boxed(lean_object* v_inst_59_, lean_object* v_n_60_, lean_object* v_a_61_, lean_object* v_t_62_, lean_object* v_i_63_, lean_object* v_M_64_, lean_object* v_s_65_, lean_object* v_s_x27_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_Formalism_L2_Forms_blkMat___redArg(v_inst_59_, v_n_60_, v_a_61_, v_t_62_, v_i_63_, v_M_64_, v_s_65_, v_s_x27_66_);
lean_dec(v_s_x27_66_);
lean_dec(v_s_65_);
lean_dec(v_i_63_);
lean_dec(v_t_62_);
lean_dec(v_a_61_);
lean_dec(v_n_60_);
lean_dec_ref(v_inst_59_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat(lean_object* v_k_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_a_71_, lean_object* v_t_72_, lean_object* v_i_73_, lean_object* v_M_74_, lean_object* v_s_75_, lean_object* v_s_x27_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_tree_Formalism_L2_Forms_blkMat___redArg(v_inst_69_, v_n_70_, v_a_71_, v_t_72_, v_i_73_, v_M_74_, v_s_75_, v_s_x27_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_blkMat___boxed(lean_object* v_k_78_, lean_object* v_inst_79_, lean_object* v_n_80_, lean_object* v_a_81_, lean_object* v_t_82_, lean_object* v_i_83_, lean_object* v_M_84_, lean_object* v_s_85_, lean_object* v_s_x27_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_L2_Forms_blkMat(v_k_78_, v_inst_79_, v_n_80_, v_a_81_, v_t_82_, v_i_83_, v_M_84_, v_s_85_, v_s_x27_86_);
lean_dec(v_s_x27_86_);
lean_dec(v_s_85_);
lean_dec(v_i_83_);
lean_dec(v_t_82_);
lean_dec(v_a_81_);
lean_dec(v_n_80_);
lean_dec_ref(v_inst_79_);
return v_res_87_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_IsLocBasis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_PsiZeroNontrivialCharacter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_IsLocBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
