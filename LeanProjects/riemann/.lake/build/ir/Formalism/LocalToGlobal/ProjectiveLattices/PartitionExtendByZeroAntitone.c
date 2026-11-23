// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.Divisibility.WeightAlgebra public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ext0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ext0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ext0(lean_object* v_p_1_, lean_object* v_f_2_, lean_object* v_i_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_i_3_, v_p_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
lean_dec(v_i_3_);
lean_dec_ref(v_f_2_);
v___x_5_ = lean_unsigned_to_nat(0u);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_1(v_f_2_, v_i_3_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_ext0___boxed(lean_object* v_p_7_, lean_object* v_f_8_, lean_object* v_i_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_L2_Pj_ext0(v_p_7_, v_f_8_, v_i_9_);
lean_dec(v_p_7_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PartitionExtendByZeroAntitone(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
