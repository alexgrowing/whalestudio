// Lean compiler output
// Module: Lib.Shimura.Eigenspace
// Imports: public import Init public meta import Init public import Lib.Cohomology.WoodsHole public import Lib.PadicComparison.CrystallineFrobenius public import Lib.PadicHodge.Limit.CrystallineLimit public import Lib.Shimura.CongruenceRelation.EichlerShimura public import Lib.Shimura.Transfer.Lefschetz
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
lean_object* initialize_GRH_Lib_Cohomology_WoodsHole(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_CrystallineFrobenius(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Limit_CrystallineLimit(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_CongruenceRelation_EichlerShimura(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Transfer_Lefschetz(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_Eigenspace(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_WoodsHole(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_CrystallineFrobenius(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicHodge_Limit_CrystallineLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_CongruenceRelation_EichlerShimura(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Transfer_Lefschetz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
