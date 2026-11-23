// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianColumns.ColsHerm
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianColumns.CompletionIntegersIff public import Formalism.LocalToGlobal.HermitianColumns.Lev0Tied public import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty public import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter public import Formalism.LocalToGlobal.HermitianColumns.StepLevelQ public import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_FullTied_cols___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_FullTied_cols(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_FullTied_cols___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_FullTied_cols___redArg(lean_object* v_X_1_){
_start:
{
lean_object* v_toAllTied_2_; lean_object* v_base_3_; lean_object* v_levelZeroCompatibility_4_; lean_object* v_fvI_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_toAllTied_2_ = lean_ctor_get(v_X_1_, 0);
lean_inc_ref(v_toAllTied_2_);
v_base_3_ = lean_ctor_get(v_toAllTied_2_, 0);
lean_inc_ref(v_base_3_);
v_levelZeroCompatibility_4_ = lean_ctor_get(v_X_1_, 1);
v_fvI_5_ = lean_ctor_get(v_X_1_, 3);
v_isSharedCheck_14_ = !lean_is_exclusive(v_X_1_);
if (v_isSharedCheck_14_ == 0)
{
lean_object* v_unused_15_; lean_object* v_unused_16_; 
v_unused_15_ = lean_ctor_get(v_X_1_, 2);
lean_dec(v_unused_15_);
v_unused_16_ = lean_ctor_get(v_X_1_, 0);
lean_dec(v_unused_16_);
v___x_7_ = v_X_1_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_fvI_5_);
lean_inc(v_levelZeroCompatibility_4_);
lean_dec(v_X_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_atT_9_; lean_object* v_toHermCols_10_; lean_object* v___x_12_; 
v_atT_9_ = lean_ctor_get(v_toAllTied_2_, 1);
lean_inc_ref(v_atT_9_);
lean_dec_ref(v_toAllTied_2_);
v_toHermCols_10_ = lean_ctor_get(v_base_3_, 0);
lean_inc_ref(v_toHermCols_10_);
lean_dec_ref(v_base_3_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v_levelZeroCompatibility_4_);
lean_ctor_set(v___x_7_, 1, v_atT_9_);
lean_ctor_set(v___x_7_, 0, v_toHermCols_10_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_toHermCols_10_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_atT_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 2, v_levelZeroCompatibility_4_);
lean_ctor_set(v_reuseFailAlloc_13_, 3, v_fvI_5_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_FullTied_cols(lean_object* v_D_17_, lean_object* v_X_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_L2_Herm_FullTied_cols___redArg(v_X_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_FullTied_cols___boxed(lean_object* v_D_20_, lean_object* v_X_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_Herm_FullTied_cols(v_D_20_, v_X_21_);
lean_dec_ref(v_D_20_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_CompletionIntegersIff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_Lev0Tied(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ClsNonempty(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ZeroPointScaledByCharacter(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_StepLevelQ(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_CoordinateLatticeSelfDual(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ColsHerm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_CompletionIntegersIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_Lev0Tied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ClsNonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ZeroPointScaledByCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_StepLevelQ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_CoordinateLatticeSelfDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
