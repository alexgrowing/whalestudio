// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.FormsTied
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi public import Formalism.LocalToGlobal.HermitianForms.TransportT
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_aOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_aOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_skipOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_skipOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_fcOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_fcOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_aOf(lean_object* v_R_1_, lean_object* v_i_2_){
_start:
{
lean_object* v_k_3_; lean_object* v_m_4_; uint8_t v___x_5_; 
v_k_3_ = lean_ctor_get(v_R_1_, 1);
v_m_4_ = lean_ctor_get(v_R_1_, 2);
v___x_5_ = lean_nat_dec_lt(v_i_2_, v_m_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_1_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
v___x_7_ = lean_nat_add(v_k_3_, v_i_2_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_aOf___boxed(lean_object* v_R_8_, lean_object* v_i_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_L2_Forms_aOf(v_R_8_, v_i_9_);
lean_dec(v_i_9_);
lean_dec_ref(v_R_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_skipOf(lean_object* v_R_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_k_13_; lean_object* v_m_14_; lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_k_13_ = lean_ctor_get(v_R_11_, 1);
v_m_14_ = lean_ctor_get(v_R_11_, 2);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_i_12_, v___x_15_);
v___x_17_ = lean_nat_dec_lt(v___x_16_, v_m_14_);
lean_dec(v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_11_, v_i_12_);
return v___x_18_;
}
else
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_skipOf___boxed(lean_object* v_R_19_, lean_object* v_i_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_Forms_skipOf(v_R_19_, v_i_20_);
lean_dec(v_i_20_);
lean_dec_ref(v_R_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_fcOf(lean_object* v_R_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_k_24_; lean_object* v_m_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_k_24_ = lean_ctor_get(v_R_22_, 1);
v_m_25_ = lean_ctor_get(v_R_22_, 2);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_i_23_, v___x_26_);
v___x_28_ = lean_nat_dec_le(v_m_25_, v___x_27_);
lean_dec(v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_22_, v_i_23_);
return v___x_29_;
}
else
{
lean_inc(v_k_24_);
return v_k_24_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_fcOf___boxed(lean_object* v_R_30_, lean_object* v_i_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_L2_Forms_fcOf(v_R_30_, v_i_31_);
lean_dec(v_i_31_);
lean_dec_ref(v_R_30_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_LastCoordinateUniformizerVectorSpansOrthogonalLi(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_TransportT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_FormsTied(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_LastCoordinateUniformizerVectorSpansOrthogonalLi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_TransportT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
