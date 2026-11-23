// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementE public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg(lean_object* v_a_5_, lean_object* v_v_6_){
_start:
{
lean_object* v_fst_7_; uint8_t v___x_8_; 
v_fst_7_ = lean_ctor_get(v_v_6_, 0);
v___x_8_ = lean_nat_dec_le(v_fst_7_, v_a_5_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__0, &lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__0_once, _init_lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__1, &lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__1_once, _init_lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___closed__1);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg___boxed(lean_object* v_a_11_, lean_object* v_v_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg(v_a_11_, v_v_12_);
lean_dec_ref(v_v_12_);
lean_dec(v_a_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP(lean_object* v_r_14_, lean_object* v_n_15_, lean_object* v_a_16_, lean_object* v_v_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_GradedWeylDivisibility_lehwP___redArg(v_a_16_, v_v_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lehwP___boxed(lean_object* v_r_19_, lean_object* v_n_20_, lean_object* v_a_21_, lean_object* v_v_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_GradedWeylDivisibility_lehwP(v_r_19_, v_n_20_, v_a_21_, v_v_22_);
lean_dec_ref(v_v_22_);
lean_dec(v_a_21_);
lean_dec(v_n_20_);
lean_dec(v_r_19_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementE(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
