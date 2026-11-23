// Lean compiler output
// Module: Formalism.SuccessiveMinima.DefsNP
// Imports: public import Init public meta import Init public import Formalism.SuccessiveMinima.StatementNP
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg___lam__0(lean_object* v_a_1_, lean_object* v_n_2_, lean_object* v_b_3_, lean_object* v_toMul_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc(v_i_5_);
v___x_6_ = lean_apply_1(v_a_1_, v_i_5_);
v___x_7_ = lean_nat_sub(v_n_2_, v_i_5_);
lean_dec(v_i_5_);
v___x_8_ = lean_apply_1(v_b_3_, v___x_7_);
v___x_9_ = lean_apply_2(v_toMul_4_, v___x_6_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg___lam__0___boxed(lean_object* v_a_10_, lean_object* v_n_11_, lean_object* v_b_12_, lean_object* v_toMul_13_, lean_object* v_i_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_FN_cmul___redArg___lam__0(v_a_10_, v_n_11_, v_b_12_, v_toMul_13_, v_i_14_);
lean_dec(v_n_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg(lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_b_18_, lean_object* v_n_19_){
_start:
{
lean_object* v_toField_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_toSemiring_23_; lean_object* v_toAddCommMonoid_24_; lean_object* v___x_25_; lean_object* v_toMul_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___f_30_; lean_object* v___x_31_; 
v_toField_20_ = lean_ctor_get(v_inst_16_, 1);
v___x_21_ = lp_mathlib_Field_toSemifield___redArg(v_toField_20_);
v___x_22_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_21_);
v_toSemiring_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_toSemiring_23_);
lean_dec_ref(v___x_22_);
v_toAddCommMonoid_24_ = lean_ctor_get(v_toSemiring_23_, 0);
lean_inc_ref(v_toAddCommMonoid_24_);
v___x_25_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_23_);
v_toMul_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_toMul_26_);
lean_dec_ref(v___x_25_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_n_19_, v___x_27_);
v___x_29_ = l_List_range(v___x_28_);
v___f_30_ = lean_alloc_closure((void*)(lp_tree_Formalism_FN_cmul___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_30_, 0, v_a_17_);
lean_closure_set(v___f_30_, 1, v_n_19_);
lean_closure_set(v___f_30_, 2, v_b_18_);
lean_closure_set(v___f_30_, 3, v_toMul_26_);
v___x_31_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_24_, v___x_29_, v___f_30_);
lean_dec_ref(v_toAddCommMonoid_24_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___redArg___boxed(lean_object* v_inst_32_, lean_object* v_a_33_, lean_object* v_b_34_, lean_object* v_n_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_FN_cmul___redArg(v_inst_32_, v_a_33_, v_b_34_, v_n_35_);
lean_dec_ref(v_inst_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul(lean_object* v_K_37_, lean_object* v_inst_38_, lean_object* v_a_39_, lean_object* v_b_40_, lean_object* v_n_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_FN_cmul___redArg(v_inst_38_, v_a_39_, v_b_40_, v_n_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_cmul___boxed(lean_object* v_K_43_, lean_object* v_inst_44_, lean_object* v_a_45_, lean_object* v_b_46_, lean_object* v_n_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree_Formalism_FN_cmul(v_K_43_, v_inst_44_, v_a_45_, v_b_46_, v_n_47_);
lean_dec_ref(v_inst_44_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_StatementNP(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SuccessiveMinima_DefsNP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_StatementNP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
