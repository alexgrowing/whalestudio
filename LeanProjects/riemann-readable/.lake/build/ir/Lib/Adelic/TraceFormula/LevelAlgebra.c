// Lean compiler output
// Module: Lib.Adelic.TraceFormula.LevelAlgebra
// Imports: public import Init public meta import Init public import Lib.Adelic.Hecke.Basic
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
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_levelAlgebra___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra(lean_object* v_G_5_, lean_object* v_M_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_00_u03c1_10_, lean_object* v_K_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_levelAlgebra___boxed(lean_object* v_G_13_, lean_object* v_M_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_00_u03c1_18_, lean_object* v_K_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_levelAlgebra(v_G_13_, v_M_14_, v_inst_15_, v_inst_16_, v_inst_17_, v_00_u03c1_18_, v_K_19_);
lean_dec(v_00_u03c1_18_);
lean_dec(v_inst_17_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Hecke_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_TraceFormula_LevelAlgebra(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Hecke_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
