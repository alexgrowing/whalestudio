// Lean compiler output
// Module: Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
// Imports: public import Init public meta import Init public import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_vecMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___lam__0(lean_object* v_A_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; 
v_fst_3_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_p_2_);
v___x_5_ = lean_apply_2(v_A_1_, v_fst_3_, v_snd_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_f_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_lt(v___y_8_, v___y_9_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
lean_dec(v_f_7_);
v___x_11_ = lean_nat_dec_eq(v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec(v___y_8_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v_toSemiring_14_; lean_object* v___x_15_; lean_object* v_toZero_16_; 
v___x_12_ = lp_mathlib_Field_toSemifield___redArg(v_inst_6_);
lean_dec_ref(v_inst_6_);
v___x_13_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_12_);
v_toSemiring_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref(v_toSemiring_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_14_);
v_toZero_16_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_toZero_16_);
lean_dec_ref(v___x_15_);
return v_toZero_16_;
}
else
{
lean_object* v___x_17_; lean_object* v_toRing_18_; lean_object* v___x_19_; lean_object* v_toAddMonoidWithOne_20_; lean_object* v_toOne_21_; 
v___x_17_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_6_);
v_toRing_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_toRing_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_18_);
v_toAddMonoidWithOne_20_ = lean_ctor_get(v___x_19_, 1);
lean_inc_ref(v_toAddMonoidWithOne_20_);
lean_dec_ref(v___x_19_);
v_toOne_21_ = lean_ctor_get(v_toAddMonoidWithOne_20_, 2);
lean_inc(v_toOne_21_);
lean_dec_ref(v_toAddMonoidWithOne_20_);
return v_toOne_21_;
}
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec_ref(v_inst_6_);
v___x_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_22_, 0, v___y_8_);
lean_ctor_set(v___x_22_, 1, v___y_9_);
v___x_23_ = lean_apply_1(v_f_7_, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg(lean_object* v_inst_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v___f_26_ = ((lean_object*)(lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___closed__0));
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg___lam__1), 4, 1);
lean_closure_set(v___f_27_, 0, v_inst_25_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___f_26_);
lean_ctor_set(v___x_28_, 1, v___f_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv(lean_object* v_F_29_, lean_object* v_inst_30_, lean_object* v_n_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___redArg(v_inst_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv___boxed(lean_object* v_F_33_, lean_object* v_inst_34_, lean_object* v_n_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_upperEquiv(v_F_33_, v_inst_34_, v_n_35_);
lean_dec(v_n_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg___lam__0(lean_object* v___x_37_, lean_object* v___x_38_, lean_object* v_g_39_, lean_object* v_v_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_inv_42_; lean_object* v___x_43_; 
v_inv_42_ = lean_ctor_get(v_g_39_, 1);
lean_inc(v_inv_42_);
lean_dec_ref(v_g_39_);
v___x_43_ = lp_mathlib_Matrix_vecMul___redArg(v___x_37_, v___x_38_, v_v_40_, v_inv_42_, v___y_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg(lean_object* v_inst_44_, lean_object* v_n_45_){
_start:
{
lean_object* v_toCommRing_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___f_50_; 
v_toCommRing_46_ = lean_ctor_get(v_inst_44_, 0);
v___x_47_ = l_List_finRange(v_n_45_);
v___x_48_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_46_);
v___x_49_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_48_);
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg___lam__0), 5, 2);
lean_closure_set(v___f_50_, 0, v___x_49_);
lean_closure_set(v___f_50_, 1, v___x_47_);
return v___f_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg___boxed(lean_object* v_inst_51_, lean_object* v_n_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg(v_inst_51_, v_n_52_);
lean_dec_ref(v_inst_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction(lean_object* v_F_54_, lean_object* v_inst_55_, lean_object* v_n_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___redArg(v_inst_55_, v_n_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction___boxed(lean_object* v_F_58_, lean_object* v_inst_59_, lean_object* v_n_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_rowAction(v_F_58_, v_inst_59_, v_n_60_);
lean_dec_ref(v_inst_59_);
return v_res_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
