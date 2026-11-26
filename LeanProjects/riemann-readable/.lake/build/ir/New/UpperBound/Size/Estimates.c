// Lean compiler output
// Module: New.UpperBound.Size.Estimates
// Imports: public import Init public meta import Init public import New.UpperBound.Size.ClassCount
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
lean_object* lp_GRH_New_Data_halfGap___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_offWeight___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack___redArg(lean_object* v_D_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___y_4_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_dec_eq(v_i_2_, v___x_9_);
if (v___x_10_ == 0)
{
v___y_4_ = v___x_9_;
goto v___jp_3_;
}
else
{
lean_object* v_natB_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_natB_11_ = lean_ctor_get(v_D_1_, 2);
v___x_12_ = lp_GRH_New_Data_offWeight___redArg(v_D_1_);
v___x_13_ = lean_nat_add(v_natB_11_, v___x_12_);
lean_dec(v___x_12_);
v___y_4_ = v___x_13_;
goto v___jp_3_;
}
v___jp_3_:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lp_GRH_New_Data_halfGap___redArg(v_D_1_);
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = lean_nat_pow(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_nat_add(v___y_4_, v___x_7_);
lean_dec(v___x_7_);
lean_dec(v___y_4_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack___redArg___boxed(lean_object* v_D_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_Data_rowSlack___redArg(v_D_14_, v_i_15_);
lean_dec(v_i_15_);
lean_dec_ref(v_D_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack(lean_object* v_P_17_, lean_object* v_D_18_, lean_object* v_i_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_GRH_New_Data_rowSlack___redArg(v_D_18_, v_i_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowSlack___boxed(lean_object* v_P_21_, lean_object* v_D_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_Data_rowSlack(v_P_21_, v_D_22_, v_i_23_);
lean_dec(v_i_23_);
lean_dec_ref(v_D_22_);
lean_dec_ref(v_P_21_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Size_ClassCount(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Size_Estimates(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_Size_ClassCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
