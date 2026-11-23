// Lean compiler output
// Module: Formalism.DoubleCosetMeasures.StatementV
// Imports: public import Init public meta import Init public import Formalism.DoubleCosetMeasures.StatementZ
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
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_GLint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_GLint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_congSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_congSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_GLint(lean_object* v_F_1_, lean_object* v_inst_2_, lean_object* v_O_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_GLint___boxed(lean_object* v_F_6_, lean_object* v_inst_7_, lean_object* v_O_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_DoubleCosetMeasures_GLint(v_F_6_, v_inst_7_, v_O_8_, v_a_9_);
lean_dec(v_a_9_);
lean_dec_ref(v_inst_7_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_congSub(lean_object* v_F_11_, lean_object* v_inst_12_, lean_object* v_O_13_, lean_object* v_00_u03d6_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DoubleCosetMeasures_congSub___boxed(lean_object* v_F_17_, lean_object* v_inst_18_, lean_object* v_O_19_, lean_object* v_00_u03d6_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_DoubleCosetMeasures_congSub(v_F_17_, v_inst_18_, v_O_19_, v_00_u03d6_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec(v_00_u03d6_20_);
lean_dec_ref(v_inst_18_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_DoubleCosetMeasures_StatementZ(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_DoubleCosetMeasures_StatementV(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DoubleCosetMeasures_StatementZ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
