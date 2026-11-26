// Lean compiler output
// Module: Lib.General.Algebra.SharpMinors
// Imports: public import Init public meta import Init public import Lib.General.Algebra.FittingIdealsAndLengths
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
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Selmer_matrixKernel___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel(lean_object* v_O_5_, lean_object* v_r_6_, lean_object* v_k_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_A_10_, lean_object* v_B_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_matrixKernel___boxed(lean_object* v_O_15_, lean_object* v_r_16_, lean_object* v_k_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_A_20_, lean_object* v_B_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_Selmer_matrixKernel(v_O_15_, v_r_16_, v_k_17_, v_inst_18_, v_inst_19_, v_A_20_, v_B_21_, v_inst_22_, v_inst_23_);
lean_dec(v_inst_23_);
lean_dec_ref(v_inst_22_);
lean_dec(v_A_20_);
lean_dec(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice___redArg(){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice___redArg___boxed(lean_object* v___dummy_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_Selmer_rowLattice___redArg();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice(lean_object* v_O_29_, lean_object* v_r_30_, lean_object* v_k_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_A_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rowLattice___boxed(lean_object* v_O_37_, lean_object* v_r_38_, lean_object* v_k_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_A_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_Selmer_rowLattice(v_O_37_, v_r_38_, v_k_39_, v_inst_40_, v_inst_41_, v_A_42_, v_a_43_);
lean_dec(v_a_43_);
lean_dec(v_A_42_);
lean_dec_ref(v_inst_41_);
lean_dec_ref(v_inst_40_);
return v_res_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_FittingIdealsAndLengths(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Algebra_SharpMinors(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Algebra_FittingIdealsAndLengths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
