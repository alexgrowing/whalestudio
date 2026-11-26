// Lean compiler output
// Module: Lib.GaloisRep.Main.SeedRepresentation
// Imports: public import Init public meta import Init public import Lib.ClassField.Avatar.HeckeBaseChange public import Lib.GaloisRep.KillingPolynomials public import Lib.GaloisRep.Main.CuspidalTypes public import Lib.Shimura.Eigenspace public import Lib.Shimura.IntegralModel.PELDataExistence public import Lib.Shimura.IntegralModel.TowerExistence public import Lib.Shimura.ThetaModuli.UniversalFamily public import Lib.Shimura.Transfer.WeightOccurs
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
lean_object* initialize_GRH_Lib_ClassField_Avatar_HeckeBaseChange(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_KillingPolynomials(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Main_CuspidalTypes(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Eigenspace(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_IntegralModel_PELDataExistence(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_IntegralModel_TowerExistence(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_UniversalFamily(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Transfer_WeightOccurs(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_Main_SeedRepresentation(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Avatar_HeckeBaseChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_KillingPolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_Main_CuspidalTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Eigenspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_IntegralModel_PELDataExistence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_IntegralModel_TowerExistence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaModuli_UniversalFamily(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Transfer_WeightOccurs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
