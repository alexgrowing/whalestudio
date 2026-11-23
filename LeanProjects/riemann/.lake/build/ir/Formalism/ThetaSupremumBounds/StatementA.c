// Lean compiler output
// Module: Formalism.ThetaSupremumBounds.StatementA
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LogFactorialIndices.StatementSize
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
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
extern lean_object* lp_mathlib_Nat_instCommMonoid;
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(lean_object*);
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
static const lean_closure_object lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__0_value)} };
static const lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__1 = (const lean_object*)&lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_DimensionVariation_mono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_DimensionVariation_mono___redArg___closed__0_value;
static lean_once_cell_t lp_tree_Formalism_DimensionVariation_mono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mfact___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mfact___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mfact(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_cj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_cj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0(lean_object* v_x1_4_, lean_object* v_x2_5_){
_start:
{
lean_object* v_re_6_; lean_object* v_im_7_; lean_object* v___f_8_; lean_object* v___x_9_; 
v_re_6_ = lean_ctor_get(v_x1_4_, 0);
lean_inc(v_re_6_);
v_im_7_ = lean_ctor_get(v_x1_4_, 1);
lean_inc(v_im_7_);
lean_dec_ref(v_x1_4_);
v___f_8_ = ((lean_object*)(lp_tree_Formalism_DimensionVariation_mono___redArg___lam__0___closed__1));
v___x_9_ = lp_mathlib_Complex_mulAux___redArg(v___f_8_, v_re_6_, v_im_7_, v_x2_5_);
return v___x_9_;
}
}
static lean_object* _init_lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_11_ = lp_mathlib_Complex_ofReal(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1(lean_object* v_u_12_, lean_object* v_e_13_, lean_object* v___f_14_, lean_object* v_x_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_inc(v_x_15_);
v___x_16_ = lean_apply_1(v_u_12_, v_x_15_);
v___x_17_ = lean_apply_1(v_e_13_, v_x_15_);
v___x_18_ = lean_obj_once(&lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1___closed__0, &lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1___closed__0_once, _init_lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1___closed__0);
v___x_19_ = l_npowRec___redArg(v___x_18_, v___f_14_, v___x_17_, v___x_16_);
lean_dec(v___x_17_);
return v___x_19_;
}
}
static lean_object* _init_lp_tree_Formalism_DimensionVariation_mono___redArg___closed__1(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lp_mathlib_Complex_commRing;
v___x_22_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono___redArg(lean_object* v_inst_23_, lean_object* v_u_24_, lean_object* v_e_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___f_26_ = ((lean_object*)(lp_tree_Formalism_DimensionVariation_mono___redArg___closed__0));
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_DimensionVariation_mono___redArg___lam__1), 4, 3);
lean_closure_set(v___f_27_, 0, v_u_24_);
lean_closure_set(v___f_27_, 1, v_e_25_);
lean_closure_set(v___f_27_, 2, v___f_26_);
v___x_28_ = lean_obj_once(&lp_tree_Formalism_DimensionVariation_mono___redArg___closed__1, &lp_tree_Formalism_DimensionVariation_mono___redArg___closed__1_once, _init_lp_tree_Formalism_DimensionVariation_mono___redArg___closed__1);
v___x_29_ = lp_mathlib_Finset_prod___redArg(v___x_28_, v_inst_23_, v___f_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mono(lean_object* v_00_u03ba_30_, lean_object* v_inst_31_, lean_object* v_u_32_, lean_object* v_e_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_DimensionVariation_mono___redArg(v_inst_31_, v_u_32_, v_e_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mfact___redArg___lam__0(lean_object* v_e_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_e_35_, v_x_36_);
v___x_38_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_37_);
lean_dec(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mfact___redArg(lean_object* v_inst_39_, lean_object* v_e_40_){
_start:
{
lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___f_41_ = lean_alloc_closure((void*)(lp_tree_Formalism_DimensionVariation_mfact___redArg___lam__0), 2, 1);
lean_closure_set(v___f_41_, 0, v_e_40_);
v___x_42_ = lp_mathlib_Nat_instCommMonoid;
v___x_43_ = lp_mathlib_Finset_prod___redArg(v___x_42_, v_inst_39_, v___f_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_mfact(lean_object* v_00_u03ba_44_, lean_object* v_inst_45_, lean_object* v_e_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_DimensionVariation_mfact___redArg(v_inst_45_, v_e_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_cj___redArg(lean_object* v_u_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_apply_1(v_u_48_, v_x_49_);
v___x_51_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DimensionVariation_cj(lean_object* v_00_u03ba_52_, lean_object* v_u_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_Formalism_DimensionVariation_cj___redArg(v_u_53_, v_x_54_);
return v___x_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogFactorialIndices_StatementSize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaSupremumBounds_StatementA(uint8_t builtin) {
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
res = initialize_tree_Formalism_LogFactorialIndices_StatementSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
