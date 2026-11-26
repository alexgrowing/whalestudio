// Lean compiler output
// Module: New.Spanning.Unfolding.FillingAdmissible
// Imports: public import Init public meta import Init public import Lib.General.Groups.IndexOfProduct public import New.Spanning.Unfolding.FrameMass public import New.Spanning.Unfolding.PoincareSeries public import New.Spanning.Unfolding.ReducedGroups public import New.UpperBound.Seesaw.EdgePairEvaluation public import New.UpperBound.Size.ShortColumns
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_IndexOfProduct(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_FrameMass(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_PoincareSeries(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_ReducedGroups(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_EdgePairEvaluation(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Size_ShortColumns(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_FillingAdmissible(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Groups_IndexOfProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_FrameMass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_PoincareSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_ReducedGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_EdgePairEvaluation(builtin);
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
