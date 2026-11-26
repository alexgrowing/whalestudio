// Lean compiler output
// Module: New.Spanning.Unfolding.CutoffIntegral
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure public import New.Spanning.Unfolding.Packing
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
LEAN_EXPORT lean_object* lp_GRH_New_Filling_freeRowCoords___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_freeRowCoords(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_freeRowCoords___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_imRowCoords___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_imRowCoords(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_imRowCoords___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_rowCoords___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_rowCoords(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_freeRowCoords___redArg(lean_object* v_u_1_, lean_object* v_a_2_, lean_object* v_j_3_, lean_object* v_v_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_val_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_apply_1(v_u_1_, v_v_4_);
v_val_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v_a_2_);
v___x_8_ = lean_apply_2(v_val_6_, v___x_7_, v_j_3_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_freeRowCoords(lean_object* v_E_9_, lean_object* v_inst_10_, lean_object* v_00_U0001d530_11_, lean_object* v_u_12_, lean_object* v_a_13_, lean_object* v_j_14_, lean_object* v_v_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_GRH_New_Filling_freeRowCoords___redArg(v_u_12_, v_a_13_, v_j_14_, v_v_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_freeRowCoords___boxed(lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_00_U0001d530_19_, lean_object* v_u_20_, lean_object* v_a_21_, lean_object* v_j_22_, lean_object* v_v_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_Filling_freeRowCoords(v_E_17_, v_inst_18_, v_00_U0001d530_19_, v_u_20_, v_a_21_, v_j_22_, v_v_23_);
lean_dec_ref(v_00_U0001d530_19_);
lean_dec_ref(v_inst_18_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_imRowCoords___redArg(lean_object* v_u_25_, lean_object* v_a_26_, lean_object* v_v_27_){
_start:
{
lean_object* v___x_28_; lean_object* v_val_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_im_34_; 
v___x_28_ = lean_apply_1(v_u_25_, v_v_27_);
v_val_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_val_29_);
lean_dec_ref(v___x_28_);
lean_inc(v_a_26_);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v_a_26_);
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v_a_26_);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
v___x_33_ = lean_apply_2(v_val_29_, v___x_30_, v___x_32_);
v_im_34_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_im_34_);
lean_dec_ref(v___x_33_);
return v_im_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_imRowCoords(lean_object* v_E_35_, lean_object* v_inst_36_, lean_object* v_00_U0001d530_37_, lean_object* v_u_38_, lean_object* v_a_39_, lean_object* v_v_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_GRH_New_Filling_imRowCoords___redArg(v_u_38_, v_a_39_, v_v_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_imRowCoords___boxed(lean_object* v_E_42_, lean_object* v_inst_43_, lean_object* v_00_U0001d530_44_, lean_object* v_u_45_, lean_object* v_a_46_, lean_object* v_v_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_Filling_imRowCoords(v_E_42_, v_inst_43_, v_00_U0001d530_44_, v_u_45_, v_a_46_, v_v_47_);
lean_dec_ref(v_00_U0001d530_44_);
lean_dec_ref(v_inst_43_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_rowCoords___redArg(lean_object* v_inst_49_, lean_object* v_00_U0001d530_50_, lean_object* v_u_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc_ref(v_u_51_);
lean_inc_ref(v_00_U0001d530_50_);
lean_inc_ref(v_inst_49_);
v___x_52_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_freeRowCoords___boxed), 7, 4);
lean_closure_set(v___x_52_, 0, lean_box(0));
lean_closure_set(v___x_52_, 1, v_inst_49_);
lean_closure_set(v___x_52_, 2, v_00_U0001d530_50_);
lean_closure_set(v___x_52_, 3, v_u_51_);
v___x_53_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_imRowCoords___boxed), 6, 4);
lean_closure_set(v___x_53_, 0, lean_box(0));
lean_closure_set(v___x_53_, 1, v_inst_49_);
lean_closure_set(v___x_53_, 2, v_00_U0001d530_50_);
lean_closure_set(v___x_53_, 3, v_u_51_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_rowCoords(lean_object* v_E_55_, lean_object* v_inst_56_, lean_object* v_00_U0001d530_57_, lean_object* v_u_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_GRH_New_Filling_rowCoords___redArg(v_inst_56_, v_00_U0001d530_57_, v_u_58_);
return v___x_59_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_Packing(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_CutoffIntegral(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_Packing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
