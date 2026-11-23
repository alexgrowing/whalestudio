// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint___redArg(lean_object* v_inst_1_, lean_object* v_v_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; uint8_t v___x_5_; 
v_fst_3_ = lean_ctor_get(v_v_2_, 0);
v_snd_4_ = lean_ctor_get(v_v_2_, 1);
v___x_5_ = lean_nat_dec_eq(v_fst_3_, v_snd_4_);
if (v___x_5_ == 0)
{
lean_object* v_toSemiring_6_; lean_object* v___x_7_; lean_object* v_toZero_8_; 
v_toSemiring_6_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_6_);
lean_dec_ref(v_inst_1_);
v___x_7_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_6_);
v_toZero_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toZero_8_);
lean_dec_ref(v___x_7_);
return v_toZero_8_;
}
else
{
lean_object* v___x_9_; lean_object* v_toAddMonoidWithOne_10_; lean_object* v_toOne_11_; 
v___x_9_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc_ref(v_toAddMonoidWithOne_10_);
lean_dec_ref(v___x_9_);
v_toOne_11_ = lean_ctor_get(v_toAddMonoidWithOne_10_, 2);
lean_inc(v_toOne_11_);
lean_dec_ref(v_toAddMonoidWithOne_10_);
return v_toOne_11_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint___redArg___boxed(lean_object* v_inst_12_, lean_object* v_v_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_GradedWeylDivisibility_idPoint___redArg(v_inst_12_, v_v_13_);
lean_dec_ref(v_v_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint(lean_object* v_R_15_, lean_object* v_inst_16_, lean_object* v_r_17_, lean_object* v_n_18_, lean_object* v_v_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_Formalism_GradedWeylDivisibility_idPoint___redArg(v_inst_16_, v_v_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idPoint___boxed(lean_object* v_R_21_, lean_object* v_inst_22_, lean_object* v_r_23_, lean_object* v_n_24_, lean_object* v_v_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_GradedWeylDivisibility_idPoint(v_R_21_, v_inst_22_, v_r_23_, v_n_24_, v_v_25_);
lean_dec_ref(v_v_25_);
lean_dec(v_n_24_);
lean_dec(v_r_23_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas(uint8_t builtin) {
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
