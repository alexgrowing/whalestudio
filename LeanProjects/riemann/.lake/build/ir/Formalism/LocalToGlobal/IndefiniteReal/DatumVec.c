// Lean compiler output
// Module: Formalism.LocalToGlobal.IndefiniteReal.DatumVec
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction public import Formalism.LocalToGlobal.Divisibility.DefGroup public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL___redArg(lean_object* v_inst_1_, lean_object* v_b_2_, lean_object* v_a_3_, lean_object* v_y_4_, lean_object* v_i_5_, lean_object* v_j_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_i_5_, v_b_2_);
if (v___x_7_ == 0)
{
lean_dec(v_j_6_);
lean_dec(v_i_5_);
lean_dec(v_y_4_);
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_lt(v_j_6_, v_a_3_);
if (v___x_8_ == 0)
{
lean_dec(v_j_6_);
lean_dec(v_i_5_);
lean_dec(v_y_4_);
lean_inc(v_inst_1_);
return v_inst_1_;
}
else
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_y_4_, v_i_5_, v_j_6_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL___redArg___boxed(lean_object* v_inst_10_, lean_object* v_b_11_, lean_object* v_a_12_, lean_object* v_y_13_, lean_object* v_i_14_, lean_object* v_j_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_IndefR_Datum_topL___redArg(v_inst_10_, v_b_11_, v_a_12_, v_y_13_, v_i_14_, v_j_15_);
lean_dec(v_a_12_);
lean_dec(v_b_11_);
lean_dec(v_inst_10_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL(lean_object* v_00_u03ba_17_, lean_object* v_inst_18_, lean_object* v_b_19_, lean_object* v_a_20_, lean_object* v_k_21_, lean_object* v_y_22_, lean_object* v_i_23_, lean_object* v_j_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_IndefR_Datum_topL___redArg(v_inst_18_, v_b_19_, v_a_20_, v_y_22_, v_i_23_, v_j_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Datum_topL___boxed(lean_object* v_00_u03ba_26_, lean_object* v_inst_27_, lean_object* v_b_28_, lean_object* v_a_29_, lean_object* v_k_30_, lean_object* v_y_31_, lean_object* v_i_32_, lean_object* v_j_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_IndefR_Datum_topL(v_00_u03ba_26_, v_inst_27_, v_b_28_, v_a_29_, v_k_30_, v_y_31_, v_i_32_, v_j_33_);
lean_dec(v_k_30_);
lean_dec(v_a_29_);
lean_dec(v_b_28_);
lean_dec(v_inst_27_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_LocalNewformFunction(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HeckeThetaElements_IsHeckeElt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_DatumVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_LocalNewformFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HeckeThetaElements_IsHeckeElt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
