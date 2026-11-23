// Lean compiler output
// Module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FirstLengthLePrimeBound public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem
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
lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY(lean_object*, lean_object*);
lean_object* lp_mathlib_List_Nat_antidiagonalTuple(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_mon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_mon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_mon(lean_object* v_D_1_, lean_object* v_j_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lp_tree_Formalism_MainNotions_WeightFamilies_dimY(v_D_1_, v_j_2_);
v___x_5_ = lp_mathlib_List_Nat_antidiagonalTuple(v___x_4_, v_k_3_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_mon___boxed(lean_object* v_D_6_, lean_object* v_j_7_, lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_PoleLengthBounds_mon(v_D_6_, v_j_7_, v_k_8_);
lean_dec(v_k_8_);
lean_dec(v_j_7_);
lean_dec_ref(v_D_6_);
return v_res_9_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_FirstLengthLePrimeBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ReductionUniformizerSmulMem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_MonoCount(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_FirstLengthLePrimeBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ReductionUniformizerSmulMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
