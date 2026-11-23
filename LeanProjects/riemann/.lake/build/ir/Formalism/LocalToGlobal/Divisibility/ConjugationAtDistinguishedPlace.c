// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta public import Formalism.LocalToGlobal.UnitaryNorms.IotaABijective public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_cmQb(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_cmQb___boxed(lean_object*);
static const lean_ctor_object lp_tree_Formalism_L2_DIV_coeffOrders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(625) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree_Formalism_L2_DIV_coeffOrders___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_coeffOrders___closed__0_value;
static const lean_ctor_object lp_tree_Formalism_L2_DIV_coeffOrders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)&lp_tree_Formalism_L2_DIV_coeffOrders___closed__0_value)}};
static const lean_object* lp_tree_Formalism_L2_DIV_coeffOrders___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_DIV_coeffOrders___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_coeffOrders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_coeffOrders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk___redArg(lean_object* v_x_1_){
_start:
{
lean_inc(v_x_1_);
return v_x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk___redArg___boxed(lean_object* v_x_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_L2_DIV_CoF_mk___redArg(v_x_2_);
lean_dec(v_x_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk(lean_object* v_00_u03b9_4_, lean_object* v_LL_5_, lean_object* v_x_6_, lean_object* v_hx_7_){
_start:
{
lean_inc(v_x_6_);
return v_x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CoF_mk___boxed(lean_object* v_00_u03b9_8_, lean_object* v_LL_9_, lean_object* v_x_10_, lean_object* v_hx_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_DIV_CoF_mk(v_00_u03b9_8_, v_LL_9_, v_x_10_, v_hx_11_);
lean_dec(v_x_10_);
lean_dec_ref(v_00_u03b9_8_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_cmQb(lean_object* v_00_u03b9_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_cmQb___boxed(lean_object* v_00_u03b9_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_L2_DIV_cmQb(v_00_u03b9_15_);
lean_dec_ref(v_00_u03b9_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_coeffOrders(lean_object* v_cG_23_, lean_object* v_g_u2081_24_, lean_object* v_g_u2082_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_sub(v_g_u2081_24_, v___x_26_);
v___x_28_ = lean_nat_mul(v_g_u2081_24_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_sub(v_g_u2082_25_, v___x_26_);
v___x_30_ = lean_nat_mul(v_g_u2082_25_, v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_coeffOrders___closed__1));
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_28_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v_cG_23_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_coeffOrders___boxed(lean_object* v_cG_35_, lean_object* v_g_u2081_36_, lean_object* v_g_u2082_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_L2_DIV_coeffOrders(v_cG_35_, v_g_u2081_36_, v_g_u2082_37_);
lean_dec(v_g_u2082_37_);
lean_dec(v_g_u2081_36_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_IotaABijective(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_IotaABijective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
