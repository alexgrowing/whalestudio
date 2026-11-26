// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.PieriCone
// Imports: public import Init public meta import Init public import Lib.Base
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_permStep___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_permStep___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_permStep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_permStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_permStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_permStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_permStep___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___f_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_2_, 0, v___x_1_);
return v___f_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permStep___redArg___lam__0(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_00_u03c3_5_, lean_object* v_P_6_, lean_object* v_v_7_, lean_object* v_x_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_42_; 
v_fst_10_ = lean_ctor_get(v_x_8_, 0);
v_snd_11_ = lean_ctor_get(v_x_8_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_42_ == 0)
{
v___x_13_ = v_x_8_;
v_isShared_14_ = v_isSharedCheck_42_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_snd_11_);
lean_inc(v_fst_10_);
lean_dec(v_x_8_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_42_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___y_16_; lean_object* v___x_38_; uint8_t v___x_39_; 
lean_inc(v_snd_11_);
v___x_38_ = lean_apply_1(v_v_7_, v_snd_11_);
v___x_39_ = lean_unbox(v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___f_40_; 
v___f_40_ = lean_obj_once(&lp_GRH_New_permStep___redArg___lam__0___closed__0, &lp_GRH_New_permStep___redArg___lam__0___closed__0_once, _init_lp_GRH_New_permStep___redArg___lam__0___closed__0);
v___y_16_ = v___f_40_;
goto v___jp_15_;
}
else
{
lean_object* v___x_41_; 
v___x_41_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___y_16_ = v___x_41_;
goto v___jp_15_;
}
v___jp_15_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toFun_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_36_; 
lean_inc_n(v_snd_11_, 2);
v___x_17_ = lean_apply_2(v_inst_3_, v_snd_11_, v_inst_4_);
v___x_18_ = lean_apply_1(v_00_u03c3_5_, v_snd_11_);
v_toFun_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_36_ == 0)
{
lean_object* v_unused_37_; 
v_unused_37_ = lean_ctor_get(v___x_18_, 1);
lean_dec(v_unused_37_);
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_36_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_toFun_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_36_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
lean_inc(v_fst_10_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_17_);
v___x_24_ = v___x_13_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_fst_10_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v___x_17_);
v___x_24_ = v_reuseFailAlloc_35_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = lean_apply_1(v_toFun_19_, v_fst_10_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v_snd_11_);
lean_ctor_set(v___x_21_, 0, v___x_25_);
v___x_27_ = v___x_21_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_snd_11_);
v___x_27_ = v_reuseFailAlloc_34_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; 
lean_inc(v___y_9_);
v___x_28_ = lean_apply_1(v___y_9_, v___x_24_);
v___f_29_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_29_, 0, v_P_6_);
lean_closure_set(v___f_29_, 1, v___x_28_);
v___x_30_ = lean_apply_1(v___y_9_, v___x_27_);
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_31_, 0, v___x_30_);
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_32_, 0, v___f_29_);
lean_closure_set(v___f_32_, 1, v___f_31_);
lean_inc(v___y_16_);
v___f_33_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_33_, 0, v___y_16_);
lean_closure_set(v___f_33_, 1, v___f_32_);
return v___f_33_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permStep___redArg(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_v_45_, lean_object* v_P_46_, lean_object* v_00_u03c3_47_){
_start:
{
lean_object* v___f_48_; lean_object* v___f_49_; 
v___f_48_ = lean_alloc_closure((void*)(lp_GRH_New_permStep___redArg___lam__0), 7, 5);
lean_closure_set(v___f_48_, 0, v_inst_43_);
lean_closure_set(v___f_48_, 1, v_inst_44_);
lean_closure_set(v___f_48_, 2, v_00_u03c3_47_);
lean_closure_set(v___f_48_, 3, v_P_46_);
lean_closure_set(v___f_48_, 4, v_v_45_);
v___f_49_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_49_, 0, v___f_48_);
return v___f_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permStep(lean_object* v_k_50_, lean_object* v_T_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_v_54_, lean_object* v_P_55_, lean_object* v_00_u03c3_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_GRH_New_permStep___redArg(v_inst_52_, v_inst_53_, v_v_54_, v_P_55_, v_00_u03c3_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permStep___boxed(lean_object* v_k_58_, lean_object* v_T_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_v_62_, lean_object* v_P_63_, lean_object* v_00_u03c3_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_GRH_New_permStep(v_k_58_, v_T_59_, v_inst_60_, v_inst_61_, v_v_62_, v_P_63_, v_00_u03c3_64_);
lean_dec(v_k_58_);
return v_res_65_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_PieriCone(uint8_t builtin) {
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
res = initialize_GRH_Lib_Base(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
