// Lean compiler output
// Module: Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
// Imports: public import Init public meta import Init public import Formalism.ThetaLiftIndependence.Statement public import Formalism.HermitianLattices.FinalNeighbourConstruct public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
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
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_isoSetoid(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_isoSetoid___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_isoSetoid(lean_object* v_K_1_, lean_object* v_V_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_h_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_isoSetoid___boxed(lean_object* v_K_11_, lean_object* v_V_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_h_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_isoSetoid(v_K_11_, v_V_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_h_19_);
lean_dec(v_h_19_);
lean_dec(v_inst_17_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_15_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_FinalNeighbourConstruct(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_FinalNeighbourConstruct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
