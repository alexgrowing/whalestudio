// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataLatDefs
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataGatTies public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
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
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_Ow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_Ow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW___at___00Formalism_BasicNotions_LT_imgL_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW___at___00Formalism_BasicNotions_LT_imgL_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_imgL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_imgL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_Ow(lean_object* v_D_1_, lean_object* v_w_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_Ow___boxed(lean_object* v_D_4_, lean_object* v_w_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_BasicNotions_LT_Ow(v_D_4_, v_w_5_);
lean_dec(v_w_5_);
lean_dec_ref(v_D_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW___at___00Formalism_BasicNotions_LT_imgL_spec__0(lean_object* v___x_7_, lean_object* v_Pl_8_, lean_object* v_w_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW___at___00Formalism_BasicNotions_LT_imgL_spec__0___boxed(lean_object* v___x_11_, lean_object* v_Pl_12_, lean_object* v_w_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_BasicNotions_intW___at___00Formalism_BasicNotions_LT_imgL_spec__0(v___x_11_, v_Pl_12_, v_w_13_);
lean_dec(v_w_13_);
lean_dec_ref(v_Pl_12_);
lean_dec_ref(v___x_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_imgL(lean_object* v_D_15_, lean_object* v_u_16_, lean_object* v_i_17_, lean_object* v_j_18_, lean_object* v_w_19_, lean_object* v_f_20_, lean_object* v_A_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LT_imgL___boxed(lean_object* v_D_23_, lean_object* v_u_24_, lean_object* v_i_25_, lean_object* v_j_26_, lean_object* v_w_27_, lean_object* v_f_28_, lean_object* v_A_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_BasicNotions_LT_imgL(v_D_23_, v_u_24_, v_i_25_, v_j_26_, v_w_27_, v_f_28_, v_A_29_);
lean_dec_ref(v_f_28_);
lean_dec(v_w_27_);
lean_dec(v_j_26_);
lean_dec(v_i_25_);
lean_dec(v_u_24_);
lean_dec_ref(v_D_23_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataGatTies(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataLatDefs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataGatTies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
