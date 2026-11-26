// Lean compiler output
// Module: Lib.LocalGL.Shintani.CosetRootChoice
// Imports: public import Init public meta import Init public import Lib.GaloisRep.Hilbert90.TameActions public import Lib.LocalGL.Green.HallAlgebra
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
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___redArg();
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer(lean_object* v_E_5_, lean_object* v_00_u0393_6_, lean_object* v_G_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_00_u03c0_11_, lean_object* v_00_u03c3_12_, lean_object* v_j_13_, lean_object* v_r_14_, lean_object* v_R_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer___boxed(lean_object* v_E_17_, lean_object* v_00_u0393_18_, lean_object* v_G_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_00_u03c0_23_, lean_object* v_00_u03c3_24_, lean_object* v_j_25_, lean_object* v_r_26_, lean_object* v_R_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH___private_Lib_LocalGL_Shintani_CosetRootChoice_0__New_IsRootChoice_rangeInKer(v_E_17_, v_00_u0393_18_, v_G_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_00_u03c0_23_, v_00_u03c3_24_, v_j_25_, v_r_26_, v_R_27_);
lean_dec(v_r_26_);
lean_dec(v_j_25_);
lean_dec(v_00_u03c3_24_);
lean_dec(v_00_u03c0_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Hilbert90_TameActions(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Green_HallAlgebra(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_LocalGL_Shintani_CosetRootChoice(uint8_t builtin) {
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
res = initialize_GRH_Lib_GaloisRep_Hilbert90_TameActions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_LocalGL_Green_HallAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
