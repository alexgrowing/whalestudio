// Lean compiler output
// Module: New.Determinant.AuxiliaryForms.GridFirstColumns
// Imports: public import Init public meta import Init public import New.Determinant.AuxiliaryForms.PathData public import New.Determinant.Chain.Moduli public import New.OneLift.ComparisonOperator.GluedLattices public import New.UpperBound.Seesaw.LevelIdeles
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_LevelCosets_out_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_LevelCosets_out_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___redArg(uint8_t v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__2_3_, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___redArg___boxed(lean_object* v_x_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_){
_start:
{
uint8_t v_x_24__boxed_11_; lean_object* v_res_12_; 
v_x_24__boxed_11_ = lean_unbox(v_x_8_);
v_res_12_ = lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___redArg(v_x_24__boxed_11_, v_h__1_9_, v_h__2_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter(lean_object* v_motive_13_, uint8_t v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (v_x_14_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_16_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__1_15_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__2_16_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter___boxed(lean_object* v_motive_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
uint8_t v_x_35__boxed_25_; lean_object* v_res_26_; 
v_x_35__boxed_25_ = lean_unbox(v_x_22_);
v_res_26_ = lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_triangleTwist_match__1_splitter(v_motive_21_, v_x_35__boxed_25_, v_h__1_23_, v_h__2_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_LevelCosets_out_match__1_splitter___redArg(lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_snd_30_; lean_object* v_fst_31_; lean_object* v_fst_32_; lean_object* v_snd_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_snd_30_ = lean_ctor_get(v_x_27_, 1);
v_fst_31_ = lean_ctor_get(v_x_27_, 0);
v_fst_32_ = lean_ctor_get(v_snd_30_, 0);
v_snd_33_ = lean_ctor_get(v_snd_30_, 1);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_nat_dec_eq(v_fst_32_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
lean_dec(v_h__1_28_);
v___x_36_ = lean_apply_2(v_h__2_29_, v_x_27_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
lean_inc(v_snd_33_);
lean_inc(v_fst_31_);
lean_dec(v_h__2_29_);
lean_dec_ref(v_x_27_);
v___x_37_ = lean_apply_2(v_h__1_28_, v_fst_31_, v_snd_33_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridFirstColumns_0__New_Data_LevelCosets_out_match__1_splitter(lean_object* v_motive_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
lean_object* v_snd_42_; lean_object* v_fst_43_; lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v_snd_42_ = lean_ctor_get(v_x_39_, 1);
v_fst_43_ = lean_ctor_get(v_x_39_, 0);
v_fst_44_ = lean_ctor_get(v_snd_42_, 0);
v_snd_45_ = lean_ctor_get(v_snd_42_, 1);
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_nat_dec_eq(v_fst_44_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; 
lean_dec(v_h__1_40_);
v___x_48_ = lean_apply_2(v_h__2_41_, v_x_39_, lean_box(0));
return v___x_48_;
}
else
{
lean_object* v___x_49_; 
lean_inc(v_snd_45_);
lean_inc(v_fst_43_);
lean_dec(v_h__2_41_);
lean_dec_ref(v_x_39_);
v___x_49_ = lean_apply_2(v_h__1_40_, v_fst_43_, v_snd_45_);
return v___x_49_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_PathData(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Chain_Moduli(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_GluedLattices(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_LevelIdeles(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_GridFirstColumns(uint8_t builtin) {
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
res = initialize_GRH_New_Determinant_AuxiliaryForms_PathData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Chain_Moduli(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_GluedLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_LevelIdeles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
