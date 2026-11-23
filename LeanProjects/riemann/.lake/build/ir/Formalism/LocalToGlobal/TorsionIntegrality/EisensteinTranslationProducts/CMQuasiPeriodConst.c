// Lean compiler output
// Module: Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
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
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_cmForm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_cmForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_cmForm(lean_object* v_a_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v_m_4_, lean_object* v_n_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = l_Int_pow(v_m_4_, v___x_6_);
v___x_8_ = lean_int_mul(v_a_1_, v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_int_mul(v_b_2_, v_m_4_);
v___x_10_ = lean_int_mul(v___x_9_, v_n_5_);
lean_dec(v___x_9_);
v___x_11_ = lean_int_add(v___x_8_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v___x_8_);
v___x_12_ = l_Int_pow(v_n_5_, v___x_6_);
v___x_13_ = lean_int_mul(v_c_3_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_int_add(v___x_11_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_cmForm___boxed(lean_object* v_a_15_, lean_object* v_b_16_, lean_object* v_c_17_, lean_object* v_m_18_, lean_object* v_n_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_Th1_F_cmForm(v_a_15_, v_b_16_, v_c_17_, v_m_18_, v_n_19_);
lean_dec(v_n_19_);
lean_dec(v_m_18_);
lean_dec(v_c_17_);
lean_dec(v_b_16_);
lean_dec(v_a_15_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
