// Lean compiler output
// Module: Formalism.LocalRingCardinality.SpanPowerMembership.Places
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataRows public import Formalism.LocalRingCardinality.DataArith
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
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* lp_mathlib_NumberField_RingOfIntegers_mapRingEquiv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_IsDedekindDomain_HeightOneSpectrum_equivOfRingEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_conjW___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_conjW(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
lean_inc(v_inst_2_);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_inst_2_);
lean_ctor_set(v___x_3_, 1, v_inst_2_);
v___x_4_ = lp_mathlib_NumberField_RingOfIntegers_mapRingEquiv___redArg(v_inst_1_, v_inst_1_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg___boxed(lean_object* v_inst_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg(v_inst_5_, v_inst_6_);
lean_dec_ref(v_inst_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO(lean_object* v_K_8_, lean_object* v_inst_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg(v_inst_9_, v_inst_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO(v_K_12_, v_inst_13_, v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_conjW___redArg(lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_w_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_toFun_22_; lean_object* v___x_23_; 
lean_inc_ref(v_inst_16_);
v___x_19_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_16_);
v___x_20_ = lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_starO___redArg(v_inst_16_, v_inst_17_);
lean_dec_ref(v_inst_16_);
lean_inc_ref(v___x_19_);
v___x_21_ = lp_mathlib_IsDedekindDomain_HeightOneSpectrum_equivOfRingEquiv___redArg(v___x_19_, v___x_19_, v___x_20_);
v_toFun_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_toFun_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lean_apply_1(v_toFun_22_, v_w_18_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_conjW(lean_object* v_K_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_w_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_BasicNotions_Examples_u2082_PlacesToy_conjW___redArg(v_inst_25_, v_inst_26_, v_w_27_);
return v___x_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataRows(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Places(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
