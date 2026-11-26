// Lean compiler output
// Module: Lib.Cohomology.ProperBaseChange.PlaceSpace
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.FilteredLimits
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Variety_ResiduePlace_killingPlaces___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces(lean_object* v_Z_5_, lean_object* v_D_6_, lean_object* v_P_7_, lean_object* v_s_8_, lean_object* v_00_u03be_9_, lean_object* v_z_10_, lean_object* v_I_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ResiduePlace_killingPlaces___boxed(lean_object* v_Z_13_, lean_object* v_D_14_, lean_object* v_P_15_, lean_object* v_s_16_, lean_object* v_00_u03be_17_, lean_object* v_z_18_, lean_object* v_I_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_Variety_ResiduePlace_killingPlaces(v_Z_13_, v_D_14_, v_P_15_, v_s_16_, v_00_u03be_17_, v_z_18_, v_I_19_);
lean_dec(v_z_18_);
lean_dec(v_00_u03be_17_);
lean_dec(v_s_16_);
lean_dec_ref(v_P_15_);
lean_dec_ref(v_D_14_);
lean_dec_ref(v_Z_13_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_FilteredLimits(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_ProperBaseChange_PlaceSpace(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_FilteredLimits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
