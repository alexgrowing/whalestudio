// Lean compiler output
// Module: Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedGal public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc public import Formalism.LocalToGlobal.NormalizedHeckeFactors.NormalizedHeckeData
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
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedGal(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedHecke(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedLevel(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAutLoc(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_NormalizedHeckeData(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_NGalTied(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedGal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedHecke(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAutLoc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_NormalizedHeckeData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
