// Lean compiler output
// Module: Lib.Shimura.Uniformisation.LieExponential
// Imports: public import Init public meta import Init public import Lib.General.Analysis.HolomorphicIntegrals public import Lib.General.Geometry.GeometricPoints public import Lib.Shimura.Uniformisation.HolomorphicFamilies
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
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_instTopologicalSpaceComplexPoint___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint(lean_object* v_A_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instTopologicalSpaceComplexPoint___boxed(lean_object* v_A_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_instTopologicalSpaceComplexPoint(v_A_7_);
lean_dec_ref(v_A_7_);
return v_res_8_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Geometry_GeometricPoints(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_Uniformisation_LieExponential(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Geometry_GeometricPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
