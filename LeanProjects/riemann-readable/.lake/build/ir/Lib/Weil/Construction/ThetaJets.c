// Lean compiler output
// Module: Lib.Weil.Construction.ThetaJets
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.PolarDecomposition public import Lib.Shimura.ComplexTheta.DimensionFormula public import Lib.Weil.DualPair.Defs public import Lib.Weil.MixedModel.RealTheta
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_boxes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg___lam__0(lean_object* v_00_u03ba_1_, lean_object* v_00_u03c4_2_, lean_object* v_h_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_inc(v_h_3_);
v___x_4_ = lean_apply_2(v_00_u03ba_1_, v_00_u03c4_2_, v_h_3_);
v___x_5_ = lean_nat_mul(v_h_3_, v___x_4_);
lean_dec(v___x_4_);
lean_dec(v_h_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg___lam__1(lean_object* v_00_u03ba_6_, lean_object* v_N_7_, lean_object* v___x_8_, lean_object* v_00_u03c4_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___f_10_ = lean_alloc_closure((void*)(lp_GRH_New_boxes___redArg___lam__0), 3, 2);
lean_closure_set(v___f_10_, 0, v_00_u03ba_6_);
lean_closure_set(v___f_10_, 1, v_00_u03c4_9_);
v___x_11_ = l_List_range(v_N_7_);
v___x_12_ = lp_mathlib_Finset_sum___redArg(v___x_8_, v___x_11_, v___f_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg___lam__1___boxed(lean_object* v_00_u03ba_13_, lean_object* v_N_14_, lean_object* v___x_15_, lean_object* v_00_u03c4_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_GRH_New_boxes___redArg___lam__1(v_00_u03ba_13_, v_N_14_, v___x_15_, v_00_u03c4_16_);
lean_dec_ref(v___x_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_boxes___redArg(lean_object* v_inst_18_, lean_object* v_00_u03ba_19_, lean_object* v_N_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v___x_21_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___f_22_ = lean_alloc_closure((void*)(lp_GRH_New_boxes___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_22_, 0, v_00_u03ba_19_);
lean_closure_set(v___f_22_, 1, v_N_20_);
lean_closure_set(v___f_22_, 2, v___x_21_);
v___x_23_ = lp_mathlib_Finset_sum___redArg(v___x_21_, v_inst_18_, v___f_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_boxes(lean_object* v_00_u03a6_24_, lean_object* v_inst_25_, lean_object* v_00_u03ba_26_, lean_object* v_N_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
v___x_28_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___f_29_ = lean_alloc_closure((void*)(lp_GRH_New_boxes___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_29_, 0, v_00_u03ba_26_);
lean_closure_set(v___f_29_, 1, v_N_27_);
lean_closure_set(v___f_29_, 2, v___x_28_);
v___x_30_ = lp_mathlib_Finset_sum___redArg(v___x_28_, v_inst_25_, v___f_29_);
return v___x_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_PolarDecomposition(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ComplexTheta_DimensionFormula(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_MixedModel_RealTheta(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Construction_ThetaJets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_PolarDecomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ComplexTheta_DimensionFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_MixedModel_RealTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
