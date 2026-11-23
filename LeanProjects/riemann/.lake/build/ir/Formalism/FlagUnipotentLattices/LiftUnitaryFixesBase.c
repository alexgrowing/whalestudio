// Lean compiler output
// Module: Formalism.FlagUnipotentLattices.LiftUnitaryFixesBase
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HyperbolicPlaceProducts.Statement public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_castLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg___lam__0(lean_object* v_j_1_, lean_object* v_inst_2_, lean_object* v_A_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v_a_4_, v___x_5_);
v___x_7_ = lean_nat_dec_lt(v___x_6_, v_j_1_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v_toZero_9_; 
lean_dec(v___x_6_);
lean_dec(v_a_4_);
lean_dec(v_A_3_);
v___x_8_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_inst_2_);
v_toZero_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_toZero_9_);
lean_dec_ref(v___x_8_);
return v_toZero_9_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_2(v_A_3_, v_a_4_, v___x_6_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg___lam__0___boxed(lean_object* v_j_11_, lean_object* v_inst_12_, lean_object* v_A_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg___lam__0(v_j_11_, v_inst_12_, v_A_13_, v_a_14_);
lean_dec_ref(v_inst_12_);
lean_dec(v_j_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg(lean_object* v_inst_16_, lean_object* v_j_17_, lean_object* v_A_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_ref(v_inst_16_);
lean_inc(v_j_17_);
v___f_19_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_19_, 0, v_j_17_);
lean_closure_set(v___f_19_, 1, v_inst_16_);
lean_closure_set(v___f_19_, 2, v_A_18_);
v___x_20_ = l_List_finRange(v_j_17_);
v___x_21_ = lp_mathlib_Finset_sum___redArg(v_inst_16_, v___x_20_, v___f_19_);
lean_dec_ref(v_inst_16_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_superSum(lean_object* v_R_22_, lean_object* v_inst_23_, lean_object* v_j_24_, lean_object* v_A_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_Formalism_HermitianLatticeCounting_S6_superSum___redArg(v_inst_23_, v_j_24_, v_A_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zj___redArg(lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_H_31_, lean_object* v_r_32_, lean_object* v_F_33_, lean_object* v_F_x27_34_, lean_object* v_j_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc(v_r_32_);
v___x_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___boxed), 12, 10);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, v_inst_27_);
lean_closure_set(v___x_38_, 2, v_inst_28_);
lean_closure_set(v___x_38_, 3, lean_box(0));
lean_closure_set(v___x_38_, 4, v_inst_29_);
lean_closure_set(v___x_38_, 5, v_inst_30_);
lean_closure_set(v___x_38_, 6, v_H_31_);
lean_closure_set(v___x_38_, 7, v_r_32_);
lean_closure_set(v___x_38_, 8, v_F_33_);
lean_closure_set(v___x_38_, 9, v_F_x27_34_);
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_add(v_r_32_, v___x_39_);
lean_dec(v_r_32_);
v___x_41_ = lean_alloc_closure((void*)(l_Fin_castLE___boxed), 4, 3);
lean_closure_set(v___x_41_, 0, v_j_35_);
lean_closure_set(v___x_41_, 1, v___x_40_);
lean_closure_set(v___x_41_, 2, lean_box(0));
lean_inc_ref(v___x_41_);
v___x_42_ = lp_mathlib_Matrix_submatrix___redArg(v___x_38_, v___x_41_, v___x_41_, v_a_36_, v_a_37_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zj(lean_object* v_K_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_V_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_H_49_, lean_object* v_r_50_, lean_object* v_F_51_, lean_object* v_F_x27_52_, lean_object* v_j_53_, lean_object* v_hj_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Zj___redArg(v_inst_44_, v_inst_45_, v_inst_47_, v_inst_48_, v_H_49_, v_r_50_, v_F_51_, v_F_x27_52_, v_j_53_, v_a_55_, v_a_56_);
return v___x_57_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase(uint8_t builtin) {
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
res = initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
