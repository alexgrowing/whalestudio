// Lean compiler output
// Module: Lib.Weil.Periods.GradedLattice
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.PointLattice
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_degreeZeroPart___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_degreeZeroPart___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart___redArg___lam__0(lean_object* v_w_x27_1_, lean_object* v_w_2_, lean_object* v_toZero_3_, lean_object* v_A_4_, lean_object* v_i_5_, lean_object* v_k_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
lean_inc(v_i_5_);
v___x_7_ = lean_apply_1(v_w_x27_1_, v_i_5_);
lean_inc(v_k_6_);
v___x_8_ = lean_apply_1(v_w_2_, v_k_6_);
v___x_9_ = lean_int_dec_eq(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_7_);
if (v___x_9_ == 0)
{
lean_dec(v_k_6_);
lean_dec(v_i_5_);
lean_dec(v_A_4_);
lean_inc(v_toZero_3_);
return v_toZero_3_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_2(v_A_4_, v_i_5_, v_k_6_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart___redArg___lam__0___boxed(lean_object* v_w_x27_11_, lean_object* v_w_12_, lean_object* v_toZero_13_, lean_object* v_A_14_, lean_object* v_i_15_, lean_object* v_k_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_GRH_New_degreeZeroPart___redArg___lam__0(v_w_x27_11_, v_w_12_, v_toZero_13_, v_A_14_, v_i_15_, v_k_16_);
lean_dec(v_toZero_13_);
return v_res_17_;
}
}
static lean_object* _init_lp_GRH_New_degreeZeroPart___redArg___closed__0(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_mathlib_Equiv_refl___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart___redArg(lean_object* v_inst_19_, lean_object* v_w_x27_20_, lean_object* v_w_21_, lean_object* v_A_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_toSemiring_25_; lean_object* v___x_26_; lean_object* v_toZero_27_; lean_object* v___x_28_; lean_object* v_toFun_29_; lean_object* v___f_30_; lean_object* v___x_31_; 
v_toSemiring_25_ = lean_ctor_get(v_inst_19_, 0);
lean_inc_ref(v_toSemiring_25_);
lean_dec_ref(v_inst_19_);
v___x_26_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_25_);
v_toZero_27_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_toZero_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = lean_obj_once(&lp_GRH_New_degreeZeroPart___redArg___closed__0, &lp_GRH_New_degreeZeroPart___redArg___closed__0_once, _init_lp_GRH_New_degreeZeroPart___redArg___closed__0);
v_toFun_29_ = lean_ctor_get(v___x_28_, 0);
v___f_30_ = lean_alloc_closure((void*)(lp_GRH_New_degreeZeroPart___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_30_, 0, v_w_x27_20_);
lean_closure_set(v___f_30_, 1, v_w_21_);
lean_closure_set(v___f_30_, 2, v_toZero_27_);
lean_closure_set(v___f_30_, 3, v_A_22_);
lean_inc(v_toFun_29_);
v___x_31_ = lean_apply_3(v_toFun_29_, v___f_30_, v_a_23_, v_a_24_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_degreeZeroPart(lean_object* v_R_32_, lean_object* v_00_u03b9_33_, lean_object* v_00_u03b9_x27_34_, lean_object* v_inst_35_, lean_object* v_w_x27_36_, lean_object* v_w_37_, lean_object* v_A_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_GRH_New_degreeZeroPart___redArg(v_inst_35_, v_w_x27_36_, v_w_37_, v_A_38_, v_a_39_, v_a_40_);
return v___x_41_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_PointLattice(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Periods_GradedLattice(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_PointLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
