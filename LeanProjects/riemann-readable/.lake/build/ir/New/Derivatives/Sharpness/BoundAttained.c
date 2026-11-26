// Lean compiler output
// Module: New.Derivatives.Sharpness.BoundAttained
// Imports: public import Init public meta import Init public import New.Derivatives.Sharpness.Cases
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
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding___redArg___lam__0(lean_object* v_b_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_12_; 
v_fst_3_ = lean_ctor_get(v_x_2_, 0);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_12_ == 0)
{
lean_object* v_unused_13_; 
v_unused_13_ = lean_ctor_get(v_x_2_, 1);
lean_dec(v_unused_13_);
v___x_5_ = v_x_2_;
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_fst_3_);
lean_dec(v_x_2_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_box(0);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v___x_7_);
lean_ctor_set(v___x_5_, 0, v_b_1_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_b_1_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v___x_7_);
v___x_9_ = v_reuseFailAlloc_11_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_fst_3_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding___redArg(lean_object* v_b_14_){
_start:
{
lean_object* v___f_15_; 
v___f_15_ = lean_alloc_closure((void*)(lp_GRH_New_copyEmbedding___redArg___lam__0), 2, 1);
lean_closure_set(v___f_15_, 0, v_b_14_);
return v___f_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding(lean_object* v_X_16_, lean_object* v_k_17_, lean_object* v_b_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(lp_GRH_New_copyEmbedding___redArg___lam__0), 2, 1);
lean_closure_set(v___f_19_, 0, v_b_18_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_copyEmbedding___boxed(lean_object* v_X_20_, lean_object* v_k_21_, lean_object* v_b_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_copyEmbedding(v_X_20_, v_k_21_, v_b_22_);
lean_dec(v_k_21_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Sharpness_Cases(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_Sharpness_BoundAttained(uint8_t builtin) {
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
res = initialize_GRH_New_Derivatives_Sharpness_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
