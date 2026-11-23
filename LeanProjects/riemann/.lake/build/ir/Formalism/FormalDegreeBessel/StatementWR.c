// Lean compiler output
// Module: Formalism.FormalDegreeBessel.StatementWR
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_WSm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_WSm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cbOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cbOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cbOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_WSm(lean_object* v_m_1_, lean_object* v_E_2_, lean_object* v_inst_3_, lean_object* v_inst_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_WSm___boxed(lean_object* v_m_6_, lean_object* v_E_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_QuantumDeterminants_WSm(v_m_6_, v_E_7_, v_inst_8_, v_inst_9_);
lean_dec(v_inst_9_);
lean_dec_ref(v_inst_8_);
lean_dec(v_m_6_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cOp___redArg(lean_object* v_inst_11_, lean_object* v_l_12_, lean_object* v_f_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_inc_ref(v_x_14_);
v___x_15_ = lean_apply_1(v_x_14_, v_l_12_);
v___x_16_ = lean_apply_1(v_f_13_, v_x_14_);
v___x_17_ = lean_apply_2(v_inst_11_, v___x_15_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cOp(lean_object* v_m_18_, lean_object* v_E_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_l_22_, lean_object* v_f_23_, lean_object* v_x_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_QuantumDeterminants_cOp___redArg(v_inst_21_, v_l_22_, v_f_23_, v_x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cOp___boxed(lean_object* v_m_26_, lean_object* v_E_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_l_30_, lean_object* v_f_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_Formalism_QuantumDeterminants_cOp(v_m_26_, v_E_27_, v_inst_28_, v_inst_29_, v_l_30_, v_f_31_, v_x_32_);
lean_dec_ref(v_inst_28_);
lean_dec(v_m_26_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cbOp___redArg(lean_object* v_inst_34_, lean_object* v_l_35_, lean_object* v_f_36_, lean_object* v_x_37_){
_start:
{
lean_object* v___x_38_; lean_object* v_re_39_; lean_object* v_im_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_50_; 
lean_inc_ref(v_x_37_);
v___x_38_ = lean_apply_1(v_x_37_, v_l_35_);
v_re_39_ = lean_ctor_get(v___x_38_, 0);
v_im_40_ = lean_ctor_get(v___x_38_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_50_ == 0)
{
v___x_42_ = v___x_38_;
v_isShared_43_ = v_isSharedCheck_50_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_im_40_);
lean_inc(v_re_39_);
lean_dec(v___x_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_50_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___f_44_; lean_object* v___x_46_; 
v___f_44_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_44_, 0, v_im_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___f_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_re_39_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___f_44_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_apply_1(v_f_36_, v_x_37_);
v___x_48_ = lean_apply_2(v_inst_34_, v___x_46_, v___x_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cbOp(lean_object* v_m_51_, lean_object* v_E_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_l_55_, lean_object* v_f_56_, lean_object* v_x_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_tree_Formalism_QuantumDeterminants_cbOp___redArg(v_inst_54_, v_l_55_, v_f_56_, v_x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_cbOp___boxed(lean_object* v_m_59_, lean_object* v_E_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_l_63_, lean_object* v_f_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_QuantumDeterminants_cbOp(v_m_59_, v_E_60_, v_inst_61_, v_inst_62_, v_l_63_, v_f_64_, v_x_65_);
lean_dec_ref(v_inst_61_);
lean_dec(v_m_59_);
return v_res_66_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FormalDegreeBessel_StatementWR(uint8_t builtin) {
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
