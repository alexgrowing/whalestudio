// Lean compiler output
// Module: Lib.LocalGL.Iwahori.SortedExponents
// Imports: public import Init public meta import Init public import Lib.LocalGL.Iwahori.QuadraticRelation public import Lib.LocalGL.Shintani.LiftingGreenCharacters
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___redArg(lean_object* v_inst_1_, lean_object* v_00_u03d6_2_, lean_object* v_j_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toCommSemiring_6_; lean_object* v_toMonoid_7_; uint8_t v___x_8_; 
v___x_5_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v_toCommSemiring_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref(v_toCommSemiring_6_);
lean_dec_ref(v___x_5_);
v_toMonoid_7_ = lean_ctor_get(v_toCommSemiring_6_, 1);
lean_inc_ref(v_toMonoid_7_);
lean_dec_ref(v_toCommSemiring_6_);
v___x_8_ = lean_nat_dec_lt(v_a_4_, v_j_3_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toOne_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v___x_9_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_7_);
lean_dec_ref(v_toMonoid_7_);
v___x_10_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_9_);
v_toOne_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 1);
lean_dec(v_unused_19_);
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_toOne_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
lean_inc(v_toOne_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v_toOne_11_);
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_toOne_11_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_toOne_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
else
{
lean_dec_ref(v_toMonoid_7_);
lean_inc_ref(v_00_u03d6_2_);
return v_00_u03d6_2_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___redArg___boxed(lean_object* v_inst_20_, lean_object* v_00_u03d6_21_, lean_object* v_j_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___redArg(v_inst_20_, v_00_u03d6_21_, v_j_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec(v_j_22_);
lean_dec_ref(v_00_u03d6_21_);
lean_dec_ref(v_inst_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus(lean_object* v_F_25_, lean_object* v_inst_26_, lean_object* v_N_27_, lean_object* v_00_u03d6_28_, lean_object* v_j_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___redArg(v_inst_26_, v_00_u03d6_28_, v_j_29_, v_a_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus___boxed(lean_object* v_F_32_, lean_object* v_inst_33_, lean_object* v_N_34_, lean_object* v_00_u03d6_35_, lean_object* v_j_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH___private_Lib_LocalGL_Iwahori_SortedExponents_0__New_stepTorus(v_F_32_, v_inst_33_, v_N_34_, v_00_u03d6_35_, v_j_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec(v_j_36_);
lean_dec_ref(v_00_u03d6_35_);
lean_dec(v_N_34_);
lean_dec_ref(v_inst_33_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Iwahori_QuadraticRelation(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Shintani_LiftingGreenCharacters(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_LocalGL_Iwahori_SortedExponents(uint8_t builtin) {
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
res = initialize_GRH_Lib_LocalGL_Iwahori_QuadraticRelation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_LocalGL_Shintani_LiftingGreenCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
