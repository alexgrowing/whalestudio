// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementA public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
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
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_extNu(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_extNu___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_extNu(lean_object* v_n_1_, lean_object* v_00_u03bd_2_, lean_object* v_k_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_k_3_, v_n_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
lean_dec(v_k_3_);
lean_dec_ref(v_00_u03bd_2_);
v___x_5_ = lean_unsigned_to_nat(0u);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_1(v_00_u03bd_2_, v_k_3_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_extNu___boxed(lean_object* v_n_7_, lean_object* v_00_u03bd_8_, lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_GradedWeylDivisibility_extNu(v_n_7_, v_00_u03bd_8_, v_k_9_);
lean_dec(v_n_7_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
