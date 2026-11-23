// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.RowLatLemmas
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.RowLat public import Formalism.LocalToGlobal.Divisibility.ProjLemmas public import Formalism.LocalToGlobal.Divisibility.FramesLemmas public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
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
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_Test_x0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_Test_x0___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_DIV_Test_x0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_Test_x0___closed__1;
static lean_once_cell_t lp_tree_Formalism_L2_DIV_Test_x0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_Test_x0___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_x0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_x0___boxed(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_Test_tX___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_Test_tX___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_tX___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_tX___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_Test_tX___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_Test_tX___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_Test_tX___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_Test_tX___closed__0_value;
static const lean_ctor_object lp_tree_Formalism_L2_DIV_Test_tX___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_DIV_Test_tX___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree_Formalism_L2_DIV_Test_tX___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_DIV_Test_tX___closed__1_value;
LEAN_EXPORT const lean_object* lp_tree_Formalism_L2_DIV_Test_tX = (const lean_object*)&lp_tree_Formalism_L2_DIV_Test_tX___closed__1_value;
static lean_object* _init_lp_tree_Formalism_L2_DIV_Test_x0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_Test_x0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(5u);
v___x_4_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_Test_x0___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_x0(lean_object* v_p_7_){
_start:
{
lean_object* v_snd_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_snd_8_ = lean_ctor_get(v_p_7_, 1);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_dec_eq(v_snd_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_dec_eq(v_snd_8_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_Test_x0___closed__0, &lp_tree_Formalism_L2_DIV_Test_x0___closed__0_once, _init_lp_tree_Formalism_L2_DIV_Test_x0___closed__0);
return v___x_13_;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_Test_x0___closed__1, &lp_tree_Formalism_L2_DIV_Test_x0___closed__1_once, _init_lp_tree_Formalism_L2_DIV_Test_x0___closed__1);
return v___x_14_;
}
}
else
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_Test_x0___closed__2, &lp_tree_Formalism_L2_DIV_Test_x0___closed__2_once, _init_lp_tree_Formalism_L2_DIV_Test_x0___closed__2);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_x0___boxed(lean_object* v_p_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_L2_DIV_Test_x0(v_p_16_);
lean_dec_ref(v_p_16_);
return v_res_17_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_Test_tX___lam__0___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Rat_instNatCast___lam__0(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_tX___lam__0(lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_Test_tX___lam__0___closed__0, &lp_tree_Formalism_L2_DIV_Test_tX___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_DIV_Test_tX___lam__0___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Test_tX___lam__0___boxed(lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_DIV_Test_tX___lam__0(v_x_22_);
lean_dec_ref(v_x_22_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ProjLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_FramesLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLatLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_ProjLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_FramesLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
