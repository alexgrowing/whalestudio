// Lean compiler output
// Module: Lib.DiscreteSeries.Bruhat.BigCell
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bruhat.FloorMeasures
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
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
lean_dec(v_h__1_2_);
v_val_8_ = lean_ctor_get(v_x_1_, 0);
if (lean_obj_tag(v_val_8_) == 0)
{
lean_object* v_val_9_; 
lean_dec(v_h__2_3_);
v_val_9_ = lean_ctor_get(v_val_8_, 0);
if (lean_obj_tag(v_val_9_) == 0)
{
lean_object* v_val_10_; lean_object* v___x_11_; 
lean_inc_ref(v_val_9_);
lean_dec_ref_known(v_x_1_, 1);
lean_dec(v_h__4_5_);
v_val_10_ = lean_ctor_get(v_val_9_, 0);
lean_inc(v_val_10_);
lean_dec_ref_known(v_val_9_, 1);
v___x_11_ = lean_apply_1(v_h__3_4_, v_val_10_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
lean_dec(v_h__3_4_);
v___x_12_ = lean_apply_4(v_h__4_5_, v_x_1_, lean_box(0), lean_box(0), lean_box(0));
return v___x_12_;
}
}
else
{
lean_object* v_val_13_; lean_object* v___x_14_; 
lean_inc_ref(v_val_8_);
lean_dec_ref_known(v_x_1_, 1);
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
v_val_13_ = lean_ctor_get(v_val_8_, 0);
lean_inc(v_val_13_);
lean_dec_ref_known(v_val_8_, 1);
v___x_14_ = lean_apply_1(v_h__2_3_, v_val_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter(lean_object* v_00_U0001d530_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_, lean_object* v_h__4_21_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v_val_22_; lean_object* v___x_23_; 
lean_dec(v_h__4_21_);
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v_val_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v_x_17_, 1);
v___x_23_ = lean_apply_1(v_h__1_18_, v_val_22_);
return v___x_23_;
}
else
{
lean_object* v_val_24_; 
lean_dec(v_h__1_18_);
v_val_24_ = lean_ctor_get(v_x_17_, 0);
if (lean_obj_tag(v_val_24_) == 0)
{
lean_object* v_val_25_; 
lean_dec(v_h__2_19_);
v_val_25_ = lean_ctor_get(v_val_24_, 0);
if (lean_obj_tag(v_val_25_) == 0)
{
lean_object* v_val_26_; lean_object* v___x_27_; 
lean_inc_ref(v_val_25_);
lean_dec_ref_known(v_x_17_, 1);
lean_dec(v_h__4_21_);
v_val_26_ = lean_ctor_get(v_val_25_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v_val_25_, 1);
v___x_27_ = lean_apply_1(v_h__3_20_, v_val_26_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; 
lean_dec(v_h__3_20_);
v___x_28_ = lean_apply_4(v_h__4_21_, v_x_17_, lean_box(0), lean_box(0), lean_box(0));
return v___x_28_;
}
}
else
{
lean_object* v_val_29_; lean_object* v___x_30_; 
lean_inc_ref(v_val_24_);
lean_dec_ref_known(v_x_17_, 1);
lean_dec(v_h__4_21_);
lean_dec(v_h__3_20_);
v_val_29_ = lean_ctor_get(v_val_24_, 0);
lean_inc(v_val_29_);
lean_dec_ref_known(v_val_24_, 1);
v___x_30_ = lean_apply_1(v_h__2_19_, v_val_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter___boxed(lean_object* v_00_U0001d530_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_, lean_object* v_h__4_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH___private_Lib_DiscreteSeries_Bruhat_BigCell_0__New_Floors_FloorGroups_floorOf_match__1_splitter(v_00_U0001d530_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_, v_h__4_37_);
lean_dec_ref(v_00_U0001d530_31_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_BigCell(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
