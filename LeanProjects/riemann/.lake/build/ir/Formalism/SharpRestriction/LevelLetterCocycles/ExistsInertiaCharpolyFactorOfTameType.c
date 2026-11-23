// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations public import Formalism.PadicSubsetSums.StableGradedCounts.CardLtAddCardGtAddCardEq public import Formalism.PadicSubsetSums.StableGradedCounts.ContinuousCoeffCharpolyRev
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
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_MulEquiv_piUnits(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonalRingHom___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_MulHom_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__0(lean_object* v_toMonoid_1_, lean_object* v_i_2_){
_start:
{
lean_inc_ref(v_toMonoid_1_);
return v_toMonoid_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__0___boxed(lean_object* v_toMonoid_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__0(v_toMonoid_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec_ref(v_toMonoid_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__1(lean_object* v_r_6_, lean_object* v_toMonoid_7_, lean_object* v_j_8_, lean_object* v___y_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_lt(v_j_8_, v_r_6_);
if (v___x_10_ == 0)
{
lean_inc_ref(v___y_9_);
return v___y_9_;
}
else
{
lean_object* v___x_11_; lean_object* v_toOne_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v___x_11_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_7_);
v_toOne_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 1);
lean_dec(v_unused_20_);
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_toOne_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
lean_inc(v_toOne_12_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v_toOne_12_);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_toOne_12_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_toOne_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__1___boxed(lean_object* v_r_21_, lean_object* v_toMonoid_22_, lean_object* v_j_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__1(v_r_21_, v_toMonoid_22_, v_j_23_, v___y_24_);
lean_dec_ref(v___y_24_);
lean_dec(v_j_23_);
lean_dec_ref(v_toMonoid_22_);
lean_dec(v_r_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg(lean_object* v_inst_26_, lean_object* v_r_27_, lean_object* v_n_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_toSemiring_31_; lean_object* v_toMonoid_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v_toFun_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___f_44_; 
v___x_29_ = lp_mathlib_Field_toSemifield___redArg(v_inst_26_);
v___x_30_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_29_);
v_toSemiring_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc_ref(v_toSemiring_31_);
lean_dec_ref(v___x_30_);
v_toMonoid_32_ = lean_ctor_get(v_toSemiring_31_, 1);
lean_inc_ref_n(v_toMonoid_32_, 2);
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_33_, 0, v_toMonoid_32_);
v___x_34_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_31_);
v___x_35_ = lp_mathlib_MulEquiv_piUnits(lean_box(0), lean_box(0), v___f_33_);
lean_dec_ref(v___f_33_);
v___x_36_ = lp_mathlib_Equiv_symm___redArg(v___x_35_);
v_toFun_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_toFun_37_);
lean_dec_ref(v___x_36_);
v___f_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_38_, 0, v_r_27_);
lean_closure_set(v___f_38_, 1, v_toMonoid_32_);
v___x_39_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_39_, 0, v_n_28_);
v___x_40_ = lp_mathlib_Matrix_diagonalRingHom___redArg(v___x_34_, v___x_39_);
v___f_41_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_41_, 0, v___x_40_);
v___f_42_ = lean_alloc_closure((void*)(lp_mathlib_MulHom_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_42_, 0, v___f_38_);
v___f_43_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_43_, 0, v___f_42_);
lean_closure_set(v___f_43_, 1, v_toFun_37_);
v___f_44_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_44_, 0, v___f_43_);
lean_closure_set(v___f_44_, 1, v___f_41_);
return v___f_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg___boxed(lean_object* v_inst_45_, lean_object* v_r_46_, lean_object* v_n_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg(v_inst_45_, v_r_46_, v_n_47_);
lean_dec_ref(v_inst_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom(lean_object* v_k_49_, lean_object* v_inst_50_, lean_object* v_r_51_, lean_object* v_n_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___redArg(v_inst_50_, v_r_51_, v_n_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SumRepresentations_diagHom___boxed(lean_object* v_k_54_, lean_object* v_inst_55_, lean_object* v_r_56_, lean_object* v_n_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_MainNotions_SumRepresentations_diagHom(v_k_54_, v_inst_55_, v_r_56_, v_n_57_);
lean_dec_ref(v_inst_55_);
return v_res_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_SumRepresentations(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ContinuousCoeffCharpolyRev(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_ExistsInertiaCharpolyFactorOfTameType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_SumRepresentations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ContinuousCoeffCharpolyRev(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
