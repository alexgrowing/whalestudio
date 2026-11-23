// Lean compiler output
// Module: Formalism.LocalToGlobal.GlobalTheory.HLatOps
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.DataArith
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL___redArg(lean_object* v_A_1_, lean_object* v_L_x27_2_){
_start:
{
lean_object* v_addV_3_; lean_object* v_modV_4_; lean_object* v_modOV_5_; lean_object* v_fin_u03b9_6_; lean_object* v_dec_u03b9_7_; lean_object* v_b_8_; lean_object* v_X_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_addV_3_ = lean_ctor_get(v_A_1_, 0);
v_modV_4_ = lean_ctor_get(v_A_1_, 1);
v_modOV_5_ = lean_ctor_get(v_A_1_, 2);
v_fin_u03b9_6_ = lean_ctor_get(v_A_1_, 3);
v_dec_u03b9_7_ = lean_ctor_get(v_A_1_, 4);
v_b_8_ = lean_ctor_get(v_A_1_, 5);
v_X_9_ = lean_ctor_get(v_A_1_, 6);
v_isSharedCheck_16_ = !lean_is_exclusive(v_A_1_);
if (v_isSharedCheck_16_ == 0)
{
lean_object* v_unused_17_; 
v_unused_17_ = lean_ctor_get(v_A_1_, 7);
lean_dec(v_unused_17_);
v___x_11_ = v_A_1_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_X_9_);
lean_inc(v_b_8_);
lean_inc(v_dec_u03b9_7_);
lean_inc(v_fin_u03b9_6_);
lean_inc(v_modOV_5_);
lean_inc(v_modV_4_);
lean_inc(v_addV_3_);
lean_dec(v_A_1_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 7, v_L_x27_2_);
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_addV_3_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v_modV_4_);
lean_ctor_set(v_reuseFailAlloc_15_, 2, v_modOV_5_);
lean_ctor_set(v_reuseFailAlloc_15_, 3, v_fin_u03b9_6_);
lean_ctor_set(v_reuseFailAlloc_15_, 4, v_dec_u03b9_7_);
lean_ctor_set(v_reuseFailAlloc_15_, 5, v_b_8_);
lean_ctor_set(v_reuseFailAlloc_15_, 6, v_X_9_);
lean_ctor_set(v_reuseFailAlloc_15_, 7, v_L_x27_2_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL(lean_object* v_K_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_A_22_, lean_object* v_L_x27_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL___redArg(v_A_22_, v_L_x27_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL___boxed(lean_object* v_K_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_A_29_, lean_object* v_L_x27_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_withL(v_K_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_A_29_, v_L_x27_30_);
lean_dec(v_inst_28_);
lean_dec_ref(v_inst_26_);
return v_res_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_HLatOps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
