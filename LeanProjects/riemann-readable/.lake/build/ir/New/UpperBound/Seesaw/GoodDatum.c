// Lean compiler output
// Module: New.UpperBound.Seesaw.GoodDatum
// Imports: public import Init public meta import Init public import New.UpperBound.Seesaw.AdmissibleEvaluation public import New.UpperBound.Seesaw.LevelIdeles public import New.UpperBound.Size.ShortColumns
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
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_GoodDatum_0__New_Seesaw_exists__arrowProduct__eq__smul__finHeisenbergOp_match__1__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_GoodDatum_0__New_Seesaw_exists__arrowProduct__eq__smul__finHeisenbergOp_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_GoodDatum_0__New_Seesaw_exists__arrowProduct__eq__smul__finHeisenbergOp_match__1__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_fst_4_; 
v_fst_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_4_);
if (lean_obj_tag(v_fst_4_) == 0)
{
lean_object* v_snd_5_; lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_snd_5_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_x_1_);
v_val_6_ = lean_ctor_get(v_fst_4_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_fst_4_, 1);
v___x_7_ = lean_apply_2(v_h__1_2_, v_val_6_, v_snd_5_);
return v___x_7_;
}
else
{
lean_object* v_snd_8_; lean_object* v_val_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_snd_8_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_8_);
lean_dec_ref(v_x_1_);
v_val_9_ = lean_ctor_get(v_fst_4_, 0);
lean_inc(v_val_9_);
lean_dec_ref_known(v_fst_4_, 1);
v___x_10_ = lean_apply_2(v_h__2_3_, v_val_9_, v_snd_8_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_GoodDatum_0__New_Seesaw_exists__arrowProduct__eq__smul__finHeisenbergOp_match__1__1_splitter(lean_object* v_00_u03b9_11_, lean_object* v_00_u03b9_x27_12_, lean_object* v_00_u03b9_x27_x27_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
lean_object* v_fst_18_; 
v_fst_18_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_fst_18_);
if (lean_obj_tag(v_fst_18_) == 0)
{
lean_object* v_snd_19_; lean_object* v_val_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_17_);
v_snd_19_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_snd_19_);
lean_dec_ref(v_x_15_);
v_val_20_ = lean_ctor_get(v_fst_18_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v_fst_18_, 1);
v___x_21_ = lean_apply_2(v_h__1_16_, v_val_20_, v_snd_19_);
return v___x_21_;
}
else
{
lean_object* v_snd_22_; lean_object* v_val_23_; lean_object* v___x_24_; 
lean_dec(v_h__1_16_);
v_snd_22_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_snd_22_);
lean_dec_ref(v_x_15_);
v_val_23_ = lean_ctor_get(v_fst_18_, 0);
lean_inc(v_val_23_);
lean_dec_ref_known(v_fst_18_, 1);
v___x_24_ = lean_apply_2(v_h__2_17_, v_val_23_, v_snd_22_);
return v___x_24_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_AdmissibleEvaluation(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_LevelIdeles(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Size_ShortColumns(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Seesaw_GoodDatum(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_Seesaw_AdmissibleEvaluation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_LevelIdeles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Size_ShortColumns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
