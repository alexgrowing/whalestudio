// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___lam__1(lean_object*);
static const lean_closure_object lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___closed__0 = (const lean_object*)&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___lam__0(lean_object* v_X_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_presheaf_4_; lean_object* v_obj_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toSemiring_8_; lean_object* v_toMonoid_9_; lean_object* v___x_10_; lean_object* v_toOne_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_presheaf_4_ = lean_ctor_get(v_X_1_, 1);
lean_inc_ref(v_presheaf_4_);
lean_dec_ref(v_X_1_);
v_obj_5_ = lean_ctor_get(v_presheaf_4_, 0);
lean_inc(v_obj_5_);
lean_dec_ref(v_presheaf_4_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_obj_5_, v___x_6_);
v_toSemiring_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_toSemiring_8_);
lean_dec_ref(v___x_7_);
v_toMonoid_9_ = lean_ctor_get(v_toSemiring_8_, 1);
lean_inc_ref(v_toMonoid_9_);
lean_dec_ref(v_toSemiring_8_);
v___x_10_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_9_);
lean_dec_ref(v_toMonoid_9_);
v_toOne_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 1);
lean_dec(v_unused_19_);
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_toOne_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
lean_inc(v_toOne_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v_toOne_11_);
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_toOne_11_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_toOne_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___lam__1(lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB(lean_object* v_X_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_24_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___lam__0), 3, 1);
lean_closure_set(v___f_24_, 0, v_X_23_);
v___f_25_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_Inh_trivLB___closed__0));
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___f_25_);
lean_ctor_set(v___x_26_, 1, v___f_24_);
return v___x_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
