// Lean compiler output
// Module: Lib.GLn.Dual
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.SchurNorm public import Lib.General.LinearAlgebra.BlockEmbeddings public import Lib.General.LinearAlgebra.MatrixNormBounds
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight___redArg(lean_object* v_inst_1_, lean_object* v_kp_2_, lean_object* v_km_3_, lean_object* v_00_u03c4_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc(v_i_5_);
lean_inc(v_00_u03c4_4_);
v___x_6_ = lean_apply_2(v_kp_2_, v_00_u03c4_4_, v_i_5_);
v___x_7_ = l_List_lengthTR___redArg(v_inst_1_);
v___x_8_ = lean_nat_sub(v___x_7_, v_i_5_);
lean_dec(v_i_5_);
lean_dec(v___x_7_);
v___x_9_ = lean_apply_2(v_km_3_, v_00_u03c4_4_, v___x_8_);
v___x_10_ = lean_nat_add(v___x_6_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_6_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight___redArg___boxed(lean_object* v_inst_11_, lean_object* v_kp_12_, lean_object* v_km_13_, lean_object* v_00_u03c4_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_mixedWeight___redArg(v_inst_11_, v_kp_12_, v_km_13_, v_00_u03c4_14_, v_i_15_);
lean_dec(v_inst_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight(lean_object* v_00_u03a6_17_, lean_object* v_n_18_, lean_object* v_inst_19_, lean_object* v_kp_20_, lean_object* v_km_21_, lean_object* v_00_u03c4_22_, lean_object* v_i_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_inc(v_i_23_);
lean_inc(v_00_u03c4_22_);
v___x_24_ = lean_apply_2(v_kp_20_, v_00_u03c4_22_, v_i_23_);
v___x_25_ = l_List_lengthTR___redArg(v_inst_19_);
v___x_26_ = lean_nat_sub(v___x_25_, v_i_23_);
lean_dec(v_i_23_);
lean_dec(v___x_25_);
v___x_27_ = lean_apply_2(v_km_21_, v_00_u03c4_22_, v___x_26_);
v___x_28_ = lean_nat_add(v___x_24_, v___x_27_);
lean_dec(v___x_27_);
lean_dec(v___x_24_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_mixedWeight___boxed(lean_object* v_00_u03a6_29_, lean_object* v_n_30_, lean_object* v_inst_31_, lean_object* v_kp_32_, lean_object* v_km_33_, lean_object* v_00_u03c4_34_, lean_object* v_i_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_mixedWeight(v_00_u03a6_29_, v_n_30_, v_inst_31_, v_kp_32_, v_km_33_, v_00_u03c4_34_, v_i_35_);
lean_dec(v_inst_31_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_SchurNorm(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GLn_Dual(uint8_t builtin) {
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
res = initialize_GRH_Lib_GLn_SchurModule_SchurNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
