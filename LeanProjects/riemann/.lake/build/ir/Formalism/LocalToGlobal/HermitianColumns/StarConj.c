// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianColumns.StarConj
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm public import Formalism.LocalRingCardinality.DataExtra public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_toErrX___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_toErrX___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_toErrX(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_toErrX___lam__0(lean_object* v_toAllTied_1_, lean_object* v_u_2_){
_start:
{
lean_object* v_atT_3_; lean_object* v___x_4_; lean_object* v_piU_5_; 
v_atT_3_ = lean_ctor_get(v_toAllTied_1_, 1);
lean_inc_ref(v_atT_3_);
lean_dec_ref(v_toAllTied_1_);
v___x_4_ = lean_apply_1(v_atT_3_, v_u_2_);
v_piU_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_piU_5_);
lean_dec_ref(v___x_4_);
return v_piU_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_toErrX___lam__1(lean_object* v_toAllTied_6_, lean_object* v_u_7_, lean_object* v_v_8_){
_start:
{
lean_object* v_base_9_; lean_object* v_toHermCols_10_; lean_object* v_vT_11_; lean_object* v___x_12_; lean_object* v_toFun_13_; lean_object* v___x_14_; 
v_base_9_ = lean_ctor_get(v_toAllTied_6_, 0);
lean_inc_ref(v_base_9_);
lean_dec_ref(v_toAllTied_6_);
v_toHermCols_10_ = lean_ctor_get(v_base_9_, 0);
lean_inc_ref(v_toHermCols_10_);
lean_dec_ref(v_base_9_);
v_vT_11_ = lean_ctor_get(v_toHermCols_10_, 3);
lean_inc_ref(v_vT_11_);
lean_dec_ref(v_toHermCols_10_);
v___x_12_ = lean_apply_1(v_vT_11_, v_u_7_);
v_toFun_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_toFun_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_apply_1(v_toFun_13_, v_v_8_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_toErrX(lean_object* v_D_15_, lean_object* v_X_16_){
_start:
{
lean_object* v_toAllTied_17_; lean_object* v_levelZeroCompatibility_18_; lean_object* v_u_u2080_19_; lean_object* v___x_20_; lean_object* v_piG_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; 
v_toAllTied_17_ = lean_ctor_get(v_X_16_, 0);
lean_inc_ref_n(v_toAllTied_17_, 2);
v_levelZeroCompatibility_18_ = lean_ctor_get(v_X_16_, 1);
lean_inc_ref(v_levelZeroCompatibility_18_);
lean_dec_ref(v_X_16_);
v_u_u2080_19_ = lean_ctor_get(v_D_15_, 8);
lean_inc(v_u_u2080_19_);
lean_dec_ref(v_D_15_);
v___x_20_ = lean_apply_1(v_levelZeroCompatibility_18_, v_u_u2080_19_);
v_piG_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_piG_21_);
lean_dec_ref(v___x_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Herm_toErrX___lam__0), 2, 1);
lean_closure_set(v___f_22_, 0, v_toAllTied_17_);
v___f_23_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Herm_toErrX___lam__1), 3, 1);
lean_closure_set(v___f_23_, 0, v_toAllTied_17_);
v___x_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_24_, 0, v_piG_21_);
lean_ctor_set(v___x_24_, 1, v___f_22_);
lean_ctor_set(v___x_24_, 2, v___f_23_);
return v___x_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ColsHerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataExtra(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_StarConj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ColsHerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
