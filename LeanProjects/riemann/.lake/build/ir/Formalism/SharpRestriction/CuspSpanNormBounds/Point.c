// Lean compiler output
// Module: Formalism.SharpRestriction.CuspSpanNormBounds.Point
// Imports: public import Init public meta import Init public import Mathlib
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_dec(v_x_4_);
lean_dec(v_x_3_);
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; uint8_t v___x_15_; 
v_head_5_ = lean_ctor_get(v_x_2_, 0);
v_tail_6_ = lean_ctor_get(v_x_2_, 1);
v_fst_7_ = lean_ctor_get(v_head_5_, 0);
v_snd_8_ = lean_ctor_get(v_head_5_, 1);
v___x_15_ = lean_nat_dec_lt(v_x_3_, v_snd_8_);
if (v___x_15_ == 0)
{
goto v___jp_9_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_lt(v_x_4_, v_snd_8_);
if (v___x_16_ == 0)
{
goto v___jp_9_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_17_ = lean_nat_add(v_x_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v_x_3_);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v___x_17_, v___x_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_nat_dec_eq(v___x_19_, v_snd_8_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
lean_inc(v_fst_7_);
return v_fst_7_;
}
}
}
v___jp_9_:
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_le(v_snd_8_, v_x_3_);
if (v___x_10_ == 0)
{
lean_dec(v_x_4_);
lean_dec(v_x_3_);
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_le(v_snd_8_, v_x_4_);
if (v___x_11_ == 0)
{
lean_dec(v_x_4_);
lean_dec(v_x_3_);
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_nat_sub(v_x_3_, v_snd_8_);
lean_dec(v_x_3_);
v___x_13_ = lean_nat_sub(v_x_4_, v_snd_8_);
lean_dec(v_x_4_);
v_x_2_ = v_tail_6_;
v_x_3_ = v___x_12_;
v_x_4_ = v___x_13_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry___redArg___boxed(lean_object* v_inst_21_, lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_MainNotions_S_ptEntry___redArg(v_inst_21_, v_x_22_, v_x_23_, v_x_24_);
lean_dec(v_x_22_);
lean_dec(v_inst_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry(lean_object* v_K_26_, lean_object* v_inst_27_, lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_Formalism_MainNotions_S_ptEntry___redArg(v_inst_27_, v_x_28_, v_x_29_, v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptEntry___boxed(lean_object* v_K_32_, lean_object* v_inst_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_MainNotions_S_ptEntry(v_K_32_, v_inst_33_, v_x_34_, v_x_35_, v_x_36_);
lean_dec(v_x_34_);
lean_dec(v_inst_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat___redArg(lean_object* v_inst_38_, lean_object* v_p_39_, lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_MainNotions_S_ptEntry___redArg(v_inst_38_, v_p_39_, v_a_40_, v_b_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat___redArg___boxed(lean_object* v_inst_43_, lean_object* v_p_44_, lean_object* v_a_45_, lean_object* v_b_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_MainNotions_S_ptMat___redArg(v_inst_43_, v_p_44_, v_a_45_, v_b_46_);
lean_dec(v_p_44_);
lean_dec(v_inst_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat(lean_object* v_K_48_, lean_object* v_inst_49_, lean_object* v_i_50_, lean_object* v_p_51_, lean_object* v_a_52_, lean_object* v_b_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_tree_Formalism_MainNotions_S_ptEntry___redArg(v_inst_49_, v_p_51_, v_a_52_, v_b_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_ptMat___boxed(lean_object* v_K_55_, lean_object* v_inst_56_, lean_object* v_i_57_, lean_object* v_p_58_, lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_MainNotions_S_ptMat(v_K_55_, v_inst_56_, v_i_57_, v_p_58_, v_a_59_, v_b_60_);
lean_dec(v_p_58_);
lean_dec(v_i_57_);
lean_dec(v_inst_56_);
return v_res_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_Point(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
