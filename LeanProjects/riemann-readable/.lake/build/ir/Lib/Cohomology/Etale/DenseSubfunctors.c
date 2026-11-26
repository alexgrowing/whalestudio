// Lean compiler output
// Module: Lib.Cohomology.Etale.DenseSubfunctors
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.BijectiveComparisons
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Variety_relationLocus___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus(lean_object* v_C_5_, lean_object* v_inst_6_, lean_object* v_Y_7_, lean_object* v_W_8_, lean_object* v_00_u03b9_9_, lean_object* v_inst_10_, lean_object* v_c_11_, lean_object* v_f_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relationLocus___boxed(lean_object* v_C_14_, lean_object* v_inst_15_, lean_object* v_Y_16_, lean_object* v_W_17_, lean_object* v_00_u03b9_18_, lean_object* v_inst_19_, lean_object* v_c_20_, lean_object* v_f_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_Variety_relationLocus(v_C_14_, v_inst_15_, v_Y_16_, v_W_17_, v_00_u03b9_18_, v_inst_19_, v_c_20_, v_f_21_);
lean_dec(v_f_21_);
lean_dec_ref(v_c_20_);
lean_dec(v_inst_19_);
lean_dec_ref(v_W_17_);
lean_dec_ref(v_Y_16_);
lean_dec_ref(v_inst_15_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps___redArg(){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps___redArg___boxed(lean_object* v___dummy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Variety_elemKillingMaps___redArg();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps(lean_object* v_C_27_, lean_object* v_inst_28_, lean_object* v_00_u03b9_29_, lean_object* v_A_30_, lean_object* v_e_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elemKillingMaps___boxed(lean_object* v_C_33_, lean_object* v_inst_34_, lean_object* v_00_u03b9_35_, lean_object* v_A_36_, lean_object* v_e_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_Variety_elemKillingMaps(v_C_33_, v_inst_34_, v_00_u03b9_35_, v_A_36_, v_e_37_);
lean_dec(v_e_37_);
lean_dec(v_A_36_);
lean_dec_ref(v_00_u03b9_35_);
lean_dec_ref(v_inst_34_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_BijectiveComparisons(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_Etale_DenseSubfunctors(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_BijectiveComparisons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
