// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataKerI
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataKerP public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.DataForced
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
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_posJ___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_posJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_posJ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_posJ___redArg(lean_object* v_Gt_1_, lean_object* v_u_2_, lean_object* v_w_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_3(v_Gt_1_, v_u_2_, v_w_3_, lean_box(0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_posJ(lean_object* v_D_5_, lean_object* v_Gt_6_, lean_object* v_u_7_, lean_object* v_w_8_, lean_object* v_h_9_, lean_object* v_Fl_10_, lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_3(v_Gt_6_, v_u_7_, v_w_8_, lean_box(0));
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_posJ___boxed(lean_object* v_D_13_, lean_object* v_Gt_14_, lean_object* v_u_15_, lean_object* v_w_16_, lean_object* v_h_17_, lean_object* v_Fl_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_BasicNotions_posJ(v_D_13_, v_Gt_14_, v_u_15_, v_w_16_, v_h_17_, v_Fl_18_, v_x_19_);
lean_dec(v_x_19_);
lean_dec_ref(v_Fl_18_);
lean_dec_ref(v_D_13_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKerP(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForced(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKerI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKerP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataForced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
