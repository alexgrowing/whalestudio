// Lean compiler output
// Module: Formalism.DegreeFormula.PointDegree.PowSum
// Imports: public import Init public meta import Init public import Formalism.DegreeFormula.FlagDegFormula public import Formalism.DegreeFormula.PointDegree.PermExpInj
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
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_Perm_signAux2___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instIntCast;
extern lean_object* lp_mathlib_Real_instCommMonoid;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_PPowSum_sgnP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_PPowSum_sgnP___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_PPowSum_sgnP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_PPowSum_sgnP___redArg___lam__0(lean_object* v_N_1_, lean_object* v_00_u03c3_2_, lean_object* v___x_3_, lean_object* v_t_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_val_8_; lean_object* v___x_45__overap_9_; lean_object* v___x_10_; 
v___x_5_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_5_, 0, v_N_1_);
v___x_6_ = lean_apply_1(v_00_u03c3_2_, v_t_4_);
v___x_7_ = lp_mathlib_Equiv_Perm_signAux2___redArg(v___x_5_, v___x_3_, v___x_6_);
v_val_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_7_);
v___x_45__overap_9_ = lp_mathlib_Real_instIntCast;
v___x_10_ = lean_apply_1(v___x_45__overap_9_, v_val_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_PPowSum_sgnP___redArg(lean_object* v_inst_11_, lean_object* v_N_12_, lean_object* v_00_u03c3_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_17_; 
v___x_14_ = lp_mathlib_Real_instCommMonoid;
lean_inc(v_N_12_);
v___x_15_ = l_List_finRange(v_N_12_);
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_DegreeFormula_PPowSum_sgnP___redArg___lam__0), 4, 3);
lean_closure_set(v___f_16_, 0, v_N_12_);
lean_closure_set(v___f_16_, 1, v_00_u03c3_13_);
lean_closure_set(v___f_16_, 2, v___x_15_);
v___x_17_ = lp_mathlib_Finset_prod___redArg(v___x_14_, v_inst_11_, v___f_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_PPowSum_sgnP(lean_object* v_00_u03b9_18_, lean_object* v_inst_19_, lean_object* v_N_20_, lean_object* v_00_u03c3_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_tree_Formalism_DegreeFormula_PPowSum_sgnP___redArg(v_inst_19_, v_N_20_, v_00_u03c3_21_);
return v___x_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_DegreeFormula_FlagDegFormula(uint8_t builtin);
lean_object* initialize_tree_Formalism_DegreeFormula_PointDegree_PermExpInj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_DegreeFormula_PointDegree_PowSum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DegreeFormula_FlagDegFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DegreeFormula_PointDegree_PermExpInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
