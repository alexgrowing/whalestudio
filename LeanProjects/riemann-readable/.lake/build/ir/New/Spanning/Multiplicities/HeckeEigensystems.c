// Lean compiler output
// Module: New.Spanning.Multiplicities.HeckeEigensystems
// Imports: public import Init public meta import Init public import Lib.Adelic.TraceFormula.LevelAlgebra public import New.UpperBound.Objects.Rows
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
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Data_heckeAlgebra___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra(lean_object* v_P_5_, lean_object* v_D_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_heckeAlgebra___boxed(lean_object* v_P_8_, lean_object* v_D_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_GRH_New_Data_heckeAlgebra(v_P_8_, v_D_9_);
lean_dec_ref(v_D_9_);
lean_dec_ref(v_P_8_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_TraceFormula_LevelAlgebra(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Multiplicities_HeckeEigensystems(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_TraceFormula_LevelAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Rows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
