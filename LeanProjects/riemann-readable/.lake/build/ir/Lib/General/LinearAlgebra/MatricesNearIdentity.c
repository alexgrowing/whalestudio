// Lean compiler output
// Module: Lib.General.LinearAlgebra.MatricesNearIdentity
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.FlenstedJensen.Defs public import Lib.Shimura.ComplexTheta.AppellHumbertData
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Complex_instIntCast___lam__0(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
extern lean_object* lp_mathlib_Complex_instZero;
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_intDiagonal___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_intDiagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_intDiagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_coordProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_coordProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_intDiagonal___redArg___lam__0(lean_object* v_w_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_apply_1(v_w_1_, v_i_2_);
v___x_4_ = lp_mathlib_Complex_instIntCast___lam__0(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_intDiagonal___redArg(lean_object* v_inst_5_, lean_object* v_w_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_intDiagonal___redArg___lam__0), 2, 1);
lean_closure_set(v___f_9_, 0, v_w_6_);
v___x_10_ = lp_mathlib_Complex_instZero;
v___x_11_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_5_, v___x_10_, v___f_9_, v_a_7_, v_a_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_intDiagonal(lean_object* v_n_12_, lean_object* v_inst_13_, lean_object* v_w_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_17_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_intDiagonal___redArg___lam__0), 2, 1);
lean_closure_set(v___f_17_, 0, v_w_14_);
v___x_18_ = lp_mathlib_Complex_instZero;
v___x_19_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_13_, v___x_18_, v___f_17_, v_a_15_, v_a_16_);
return v___x_19_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_21_ = lp_mathlib_Complex_ofReal(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_23_ = lp_mathlib_Complex_ofReal(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0(lean_object* v_inst_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_apply_1(v_inst_24_, v_i_25_);
v___x_27_ = lean_unbox(v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__0, &lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__0_once, _init_lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__0);
return v___x_28_;
}
else
{
lean_object* v___x_29_; 
v___x_29_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__1, &lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__1_once, _init_lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0___closed__1);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_coordProj___redArg(lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___f_34_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_coordProj___redArg___lam__0), 2, 1);
lean_closure_set(v___f_34_, 0, v_inst_31_);
v___x_35_ = lp_mathlib_Complex_instZero;
v___x_36_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_30_, v___x_35_, v___f_34_, v_a_32_, v_a_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_coordProj(lean_object* v_n_37_, lean_object* v_inst_38_, lean_object* v_p_39_, lean_object* v_inst_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_GRH_New_DiscreteSeries_coordProj___redArg(v_inst_38_, v_inst_40_, v_a_41_, v_a_42_);
return v___x_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ComplexTheta_AppellHumbertData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatricesNearIdentity(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ComplexTheta_AppellHumbertData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
