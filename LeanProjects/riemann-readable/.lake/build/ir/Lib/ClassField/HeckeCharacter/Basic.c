// Lean compiler output
// Module: Lib.ClassField.HeckeCharacter.Basic
// Imports: public import Init public meta import Init public import Lib.ClassField.GaloisCohomology.KummerCyclicClasses public import Lib.ClassField.Places.Ideles public import Lib.GaloisRep.Hilbert90.UnitaryGroups
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
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_divStar___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_divStar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_divStar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_divStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_divStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_charsTrivialOnPrincipal___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_G_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_f_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_charsTrivialOnPrincipal___boxed(lean_object* v_E_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_G_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_f_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_charsTrivialOnPrincipal(v_E_13_, v_inst_14_, v_inst_15_, v_G_16_, v_inst_17_, v_inst_18_, v_f_19_);
lean_dec_ref(v_f_19_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_15_);
lean_dec_ref(v_inst_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_divStar___redArg___lam__0(lean_object* v_inst_21_, lean_object* v_toMul_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_val_24_; lean_object* v_inv_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_val_24_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_val_24_);
v_inv_25_ = lean_ctor_get(v_x_23_, 1);
lean_inc(v_inv_25_);
lean_dec_ref(v_x_23_);
v___x_26_ = lean_apply_1(v_inst_21_, v_inv_25_);
v___x_27_ = lean_apply_2(v_toMul_22_, v_val_24_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_divStar___redArg(lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_toMul_32_; lean_object* v___f_33_; 
v___x_30_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_inst_28_);
v___x_31_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_30_);
v_toMul_32_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_toMul_32_);
lean_dec_ref(v___x_31_);
v___f_33_ = lean_alloc_closure((void*)(lp_GRH_New_divStar___redArg___lam__0), 3, 2);
lean_closure_set(v___f_33_, 0, v_inst_29_);
lean_closure_set(v___f_33_, 1, v_toMul_32_);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_divStar___redArg___boxed(lean_object* v_inst_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_divStar___redArg(v_inst_34_, v_inst_35_);
lean_dec_ref(v_inst_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_divStar(lean_object* v_R_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_GRH_New_divStar___redArg(v_inst_38_, v_inst_39_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_divStar___boxed(lean_object* v_R_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_GRH_New_divStar(v_R_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_inst_49_);
lean_dec_ref(v_inst_45_);
return v_res_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GaloisCohomology_KummerCyclicClasses(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_Ideles(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Hilbert90_UnitaryGroups(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_Basic(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_GaloisCohomology_KummerCyclicClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Places_Ideles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_Hilbert90_UnitaryGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
