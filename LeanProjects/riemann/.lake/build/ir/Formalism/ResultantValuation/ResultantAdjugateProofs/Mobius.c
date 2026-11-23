// Lean compiler output
// Module: Formalism.ResultantValuation.ResultantAdjugateProofs.Mobius
// Imports: public import Init public meta import Init public import Formalism.ResultantValuation.SubspaceCount
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__0;
static lean_once_cell_t lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__1(void){
_start:
{
lean_object* v_zero_3_; lean_object* v___x_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v_zero_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb(lean_object* v_q_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_zero_8_; uint8_t v_isZero_9_; 
v_zero_8_ = lean_unsigned_to_nat(0u);
v_isZero_9_ = lean_nat_dec_eq(v_x_7_, v_zero_8_);
if (v_isZero_9_ == 1)
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__0, &lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__0_once, _init_lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__0);
return v___x_10_;
}
else
{
uint8_t v_isZero_11_; 
v_isZero_11_ = lean_nat_dec_eq(v_x_6_, v_zero_8_);
if (v_isZero_11_ == 1)
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__1, &lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__1_once, _init_lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___closed__1);
return v___x_12_;
}
else
{
lean_object* v_one_13_; lean_object* v_n_14_; lean_object* v_n_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_one_13_ = lean_unsigned_to_nat(1u);
v_n_14_ = lean_nat_sub(v_x_7_, v_one_13_);
v_n_15_ = lean_nat_sub(v_x_6_, v_one_13_);
v___x_16_ = lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb(v_q_5_, v_n_15_, v_n_14_);
v___x_17_ = lean_nat_add(v_n_14_, v_one_13_);
lean_dec(v_n_14_);
v___x_18_ = l_Int_pow(v_q_5_, v___x_17_);
v___x_19_ = lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb(v_q_5_, v_n_15_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v_n_15_);
v___x_20_ = lean_int_mul(v___x_18_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_int_add(v___x_16_, v___x_20_);
lean_dec(v___x_20_);
lean_dec(v___x_16_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb___boxed(lean_object* v_q_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_ResultantValuation_QBinomialResultantAdjugate_qb(v_q_22_, v_x_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_x_23_);
lean_dec(v_q_22_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_SubspaceCount(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_SubspaceCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
