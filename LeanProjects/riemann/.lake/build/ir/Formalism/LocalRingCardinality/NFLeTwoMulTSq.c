// Lean compiler output
// Module: Formalism.LocalRingCardinality.NFLeTwoMulTSq
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
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
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_NF(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_NF___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_NF(lean_object* v_R_1_){
_start:
{
lean_object* v_k_2_; lean_object* v_m_3_; lean_object* v_t_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_k_2_ = lean_ctor_get(v_R_1_, 1);
v_m_3_ = lean_ctor_get(v_R_1_, 2);
v_t_4_ = lean_ctor_get(v_R_1_, 3);
v___x_5_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_1_);
v___x_6_ = lean_unsigned_to_nat(6u);
v___x_7_ = lean_nat_add(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_nat_add(v_t_4_, v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_add(v___x_8_, v___x_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_nat_mul(v_m_3_, v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = lean_nat_add(v_k_2_, v___x_11_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Ranks_NF___boxed(lean_object* v_R_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_BasicNotions_Ranks_NF(v_R_13_);
lean_dec_ref(v_R_13_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_HeightBoundGeFourthPowerRank(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_NFLeTwoMulTSq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_HeightBoundGeFourthPowerRank(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
