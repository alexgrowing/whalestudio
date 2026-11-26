// Lean compiler output
// Module: New.Spanning.Unfolding.BesselFormula
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.Equivariant public import New.Spanning.Unfolding.PoincareSeries
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
lean_object* lp_mathlib_Equiv_subtypeEquivProp___redArg();
static lean_once_cell_t lp_GRH_New_unitSignEquiv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_unitSignEquiv___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_unitSignEquiv___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_subtypeEquivProp___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_unitSignEquiv___redArg___closed__0, &lp_GRH_New_unitSignEquiv___redArg___closed__0_once, _init_lp_GRH_New_unitSignEquiv___redArg___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_GRH_New_unitSignEquiv___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv(lean_object* v_n_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&lp_GRH_New_unitSignEquiv___redArg___closed__0, &lp_GRH_New_unitSignEquiv___redArg___closed__0_once, _init_lp_GRH_New_unitSignEquiv___redArg___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitSignEquiv___boxed(lean_object* v_n_10_, lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH_New_unitSignEquiv(v_n_10_, v_inst_11_, v_inst_12_);
lean_dec_ref(v_inst_12_);
lean_dec(v_inst_11_);
return v_res_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_Equivariant(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_PoincareSeries(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_BesselFormula(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_Equivariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_PoincareSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
