// Lean compiler output
// Module: Formalism.FrobeniusOrbits.HostThickExists
// Imports: public import Init public meta import Init public import Formalism.FrobeniusOrbits.HostOrbitsPlaces public import Formalism.FrobeniusOrbits.HostDiffSupport
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_FrobeniusOrbits_bern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_FrobeniusOrbits_bern___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___redArg(lean_object* v_inst_2_, lean_object* v_00_u03b4_3_, lean_object* v_T_4_){
_start:
{
lean_object* v___f_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___f_14_; 
v___f_5_ = ((lean_object*)(lp_tree_Formalism_FrobeniusOrbits_bern___redArg___closed__0));
v___x_6_ = l_List_lengthTR___redArg(v_T_4_);
v___x_7_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_inc(v_00_u03b4_3_);
v___x_8_ = l_npowRec___redArg(v___x_7_, v___f_5_, v___x_6_, v_00_u03b4_3_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_9_, 0, v_00_u03b4_3_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_7_);
lean_closure_set(v___f_10_, 1, v___f_9_);
v___x_11_ = l_List_lengthTR___redArg(v_inst_2_);
v___x_12_ = lean_nat_sub(v___x_11_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v___x_11_);
v___x_13_ = l_npowRec___redArg(v___x_7_, v___f_5_, v___x_12_, v___f_10_);
lean_dec(v___x_12_);
v___f_14_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_14_, 0, v___x_8_);
lean_closure_set(v___f_14_, 1, v___x_13_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___redArg___boxed(lean_object* v_inst_15_, lean_object* v_00_u03b4_16_, lean_object* v_T_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_FrobeniusOrbits_bern___redArg(v_inst_15_, v_00_u03b4_16_, v_T_17_);
lean_dec(v_T_17_);
lean_dec(v_inst_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_00_u03b4_21_, lean_object* v_T_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Formalism_FrobeniusOrbits_bern___redArg(v_inst_20_, v_00_u03b4_21_, v_T_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_bern___boxed(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_00_u03b4_26_, lean_object* v_T_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_FrobeniusOrbits_bern(v_00_u03b1_24_, v_inst_25_, v_00_u03b4_26_, v_T_27_);
lean_dec(v_T_27_);
lean_dec(v_inst_25_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostOrbitsPlaces(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostThickExists(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_HostOrbitsPlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
