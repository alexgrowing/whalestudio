// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatake
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementF public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
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
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementF(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
