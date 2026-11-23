// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Algebra_TensorProduct_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_GlobalTheory_AdLat_sg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_GlobalTheory_AdLat_sg___redArg___closed__0 = (const lean_object*)&lp_tree_GlobalTheory_AdLat_sg___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg___redArg(lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_c_7_){
_start:
{
lean_object* v___x_8_; lean_object* v_toCommSemiring_9_; lean_object* v_toSemiring_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toSemiring_13_; lean_object* v_toFun_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_2_);
v_toCommSemiring_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_toCommSemiring_9_);
lean_dec_ref(v___x_8_);
v_toSemiring_10_ = lean_ctor_get(v_inst_5_, 0);
lean_inc_ref(v_toSemiring_10_);
lean_dec_ref(v_inst_5_);
v___x_11_ = lp_mathlib_Field_toSemifield___redArg(v_inst_3_);
v___x_12_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_11_);
v_toSemiring_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc_ref_n(v_toSemiring_13_, 2);
lean_dec_ref(v___x_12_);
v_toFun_14_ = lean_ctor_get(v_c_7_, 0);
lean_inc(v_toFun_14_);
lean_dec_ref(v_c_7_);
v___f_15_ = ((lean_object*)(lp_tree_GlobalTheory_AdLat_sg___redArg___closed__0));
lean_inc_ref(v_inst_4_);
v___x_16_ = lp_mathlib_Algebra_TensorProduct_map___redArg(v_toCommSemiring_9_, v_toSemiring_13_, v_inst_4_, v_toSemiring_10_, v_inst_6_, v_toSemiring_13_, v_inst_4_, v___f_15_, v_toFun_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg___redArg___boxed(lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_c_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_GlobalTheory_AdLat_sg___redArg(v_inst_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_c_22_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg(lean_object* v_F_24_, lean_object* v_E_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_A_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_c_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_GlobalTheory_AdLat_sg___redArg(v_inst_26_, v_inst_27_, v_inst_28_, v_inst_30_, v_inst_31_, v_c_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_AdLat_sg___boxed(lean_object* v_F_34_, lean_object* v_E_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_A_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_c_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_GlobalTheory_AdLat_sg(v_F_34_, v_E_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_A_39_, v_inst_40_, v_inst_41_, v_c_42_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_inst_36_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
