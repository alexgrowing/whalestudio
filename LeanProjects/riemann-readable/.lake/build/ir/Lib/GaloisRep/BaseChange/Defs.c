// Lean compiler output
// Module: Lib.GaloisRep.BaseChange.Defs
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.Defs
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_mathlib_Nat_iterate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___redArg___lam__0(lean_object* v_00_u03c4_1_, lean_object* v_00_u03b4_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_mathlib_Nat_iterate___redArg(v_00_u03c4_1_, v_i_3_, v_00_u03b4_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___redArg(lean_object* v_inst_5_, lean_object* v_00_u03c4_6_, lean_object* v_p_7_, lean_object* v_00_u03b4_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toOne_11_; lean_object* v_toMul_12_; lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_9_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_inst_5_);
v___x_10_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_9_);
v_toOne_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_toOne_11_);
v_toMul_12_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_toMul_12_);
lean_dec_ref(v___x_10_);
v___f_13_ = lean_alloc_closure((void*)(lp_GRH_New_twistedNorm___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v_00_u03c4_6_);
lean_closure_set(v___f_13_, 1, v_00_u03b4_8_);
v___x_14_ = l_List_range(v_p_7_);
v___x_15_ = lean_box(0);
v___x_16_ = l_List_mapTR_loop___redArg(v___f_13_, v___x_14_, v___x_15_);
v___x_17_ = l_List_prod___redArg(v_toMul_12_, v_toOne_11_, v___x_16_);
lean_dec(v_toOne_11_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___redArg___boxed(lean_object* v_inst_18_, lean_object* v_00_u03c4_19_, lean_object* v_p_20_, lean_object* v_00_u03b4_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_twistedNorm___redArg(v_inst_18_, v_00_u03c4_19_, v_p_20_, v_00_u03b4_21_);
lean_dec_ref(v_inst_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm(lean_object* v_M_23_, lean_object* v_inst_24_, lean_object* v_00_u03c4_25_, lean_object* v_p_26_, lean_object* v_00_u03b4_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GRH_New_twistedNorm___redArg(v_inst_24_, v_00_u03c4_25_, v_p_26_, v_00_u03b4_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistedNorm___boxed(lean_object* v_M_29_, lean_object* v_inst_30_, lean_object* v_00_u03c4_31_, lean_object* v_p_32_, lean_object* v_00_u03b4_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_twistedNorm(v_M_29_, v_inst_30_, v_00_u03c4_31_, v_p_32_, v_00_u03b4_33_);
lean_dec_ref(v_inst_30_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_Defs(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_BaseChange_Defs(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
