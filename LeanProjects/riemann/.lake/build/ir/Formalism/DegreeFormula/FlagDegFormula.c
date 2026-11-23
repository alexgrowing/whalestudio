// Lean compiler output
// Module: Formalism.DegreeFormula.FlagDegFormula
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl___redArg(lean_object* v_inst_1_, lean_object* v_N_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_3_ = l_List_lengthTR___redArg(v_inst_1_);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_N_2_, v___x_4_);
v___x_6_ = lean_nat_mul(v_N_2_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_nat_shiftr(v___x_6_, v___x_4_);
lean_dec(v___x_6_);
v___x_8_ = lean_nat_mul(v___x_3_, v___x_7_);
lean_dec(v___x_7_);
lean_dec(v___x_3_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl___redArg___boxed(lean_object* v_inst_9_, lean_object* v_N_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_DegreeFormula_dimFl___redArg(v_inst_9_, v_N_10_);
lean_dec(v_N_10_);
lean_dec(v_inst_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl(lean_object* v_00_u03b9_12_, lean_object* v_inst_13_, lean_object* v_N_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_tree_Formalism_DegreeFormula_dimFl___redArg(v_inst_13_, v_N_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DegreeFormula_dimFl___boxed(lean_object* v_00_u03b9_16_, lean_object* v_inst_17_, lean_object* v_N_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_DegreeFormula_dimFl(v_00_u03b9_16_, v_inst_17_, v_N_18_);
lean_dec(v_N_18_);
lean_dec(v_inst_17_);
return v_res_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_DegreeFormula_FlagDegFormula(uint8_t builtin) {
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
