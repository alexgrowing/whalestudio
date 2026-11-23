// Lean compiler output
// Module: Formalism.ZetaNonvanishing.ZetaLandau
// Imports: public import Init public meta import Init public import Formalism.StatementU public import Formalism.ZetaNonvanishing.OfRealNeOfRealOfLt public import Formalism.ZetaNonvanishing.LandauEq public import Formalism.ZetaNonvanishing.MellinSgen public import Formalism.ZetaNonvanishing.MellinElem public import Formalism.ZetaNonvanishing.ZetaRealNonvanish public import Formalism.ZetaNonvanishing.LogDerivZeroFree public import Formalism.ZetaNonvanishing.MellinDeriv
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
lean_object* initialize_tree_Formalism_StatementU(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_LandauEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_MellinSgen(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_MellinElem(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_ZetaRealNonvanish(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_LogDerivZeroFree(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_MellinDeriv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ZetaNonvanishing_ZetaLandau(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_StatementU(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_LandauEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_MellinSgen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_MellinElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_ZetaRealNonvanish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_LogDerivZeroFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_MellinDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
