// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementA
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
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___redArg(lean_object* v_inst_1_, lean_object* v_r_2_, lean_object* v_f_3_, lean_object* v_a_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_a_4_, v_r_2_);
if (v___x_5_ == 0)
{
lean_dec(v_a_4_);
lean_dec(v_f_3_);
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_1(v_f_3_, v_a_4_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___redArg___boxed(lean_object* v_inst_7_, lean_object* v_r_8_, lean_object* v_f_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___redArg(v_inst_7_, v_r_8_, v_f_9_, v_a_10_);
lean_dec(v_r_8_);
lean_dec(v_inst_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_, lean_object* v_r_14_, lean_object* v_f_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___redArg(v_inst_13_, v_r_14_, v_f_15_, v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_ldiagExt___boxed(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_r_20_, lean_object* v_f_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_GradedWeylDivisibility_ldiagExt(v_00_u03b1_18_, v_inst_19_, v_r_20_, v_f_21_, v_a_22_);
lean_dec(v_r_20_);
lean_dec(v_inst_19_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
