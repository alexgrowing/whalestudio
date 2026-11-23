// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementE
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
lean_object* lp_mathlib_Complex_instNatCast___lam__0(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_REAL_Tm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___redArg___lam__0(lean_object* v_u_1_, lean_object* v_00_u03c3_2_, lean_object* v_a_3_, lean_object* v_b_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_E_7_, lean_object* v_k_8_){
_start:
{
lean_object* v_re_9_; lean_object* v_im_10_; lean_object* v___x_11_; lean_object* v_re_12_; lean_object* v_im_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_29_; 
v_re_9_ = lean_ctor_get(v_u_1_, 0);
lean_inc(v_re_9_);
v_im_10_ = lean_ctor_get(v_u_1_, 1);
lean_inc(v_im_10_);
lean_dec_ref(v_u_1_);
lean_inc(v_k_8_);
v___x_11_ = lp_mathlib_Complex_instNatCast___lam__0(v_k_8_);
v_re_12_ = lean_ctor_get(v___x_11_, 0);
v_im_13_ = lean_ctor_get(v___x_11_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_29_ == 0)
{
v___x_15_ = v___x_11_;
v_isShared_16_ = v_isSharedCheck_29_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_im_13_);
lean_inc(v_re_12_);
lean_dec(v___x_11_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_29_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_toFun_17_; lean_object* v___f_18_; lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_23_; 
v_toFun_17_ = lean_ctor_get(v_00_u03c3_2_, 0);
lean_inc(v_toFun_17_);
lean_dec_ref(v_00_u03c3_2_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_18_, 0, v_re_12_);
v___f_19_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_19_, 0, v_re_9_);
lean_closure_set(v___f_19_, 1, v___f_18_);
v___f_20_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_20_, 0, v_im_13_);
v___f_21_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_21_, 0, v_im_10_);
lean_closure_set(v___f_21_, 1, v___f_20_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___f_21_);
lean_ctor_set(v___x_15_, 0, v___f_19_);
v___x_23_ = v___x_15_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___f_19_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v___f_21_);
v___x_23_ = v_reuseFailAlloc_28_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_inc(v_k_8_);
v___x_24_ = lean_apply_1(v_toFun_17_, v_k_8_);
v___x_25_ = lean_apply_1(v_a_3_, v___x_24_);
v___x_26_ = lean_apply_1(v_b_4_, v_k_8_);
v___x_27_ = lp_tree_Formalism_REAL_Tm___redArg(v_inst_5_, v_inst_6_, v_E_7_, v___x_23_, v___x_25_, v___x_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___redArg(lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_t_32_, lean_object* v_E_33_, lean_object* v_a_34_, lean_object* v_b_35_, lean_object* v_u_36_, lean_object* v_00_u03c3_37_){
_start:
{
lean_object* v_toSemiring_38_; lean_object* v___x_39_; lean_object* v_toMul_40_; lean_object* v___x_41_; lean_object* v_toAddMonoidWithOne_42_; lean_object* v_toOne_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_toSemiring_38_ = lean_ctor_get(v_inst_30_, 0);
lean_inc_ref(v_toSemiring_38_);
v___x_39_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_38_);
v_toMul_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_toMul_40_);
lean_dec_ref(v___x_39_);
lean_inc_ref(v_inst_30_);
v___x_41_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_30_);
v_toAddMonoidWithOne_42_ = lean_ctor_get(v___x_41_, 1);
lean_inc_ref(v_toAddMonoidWithOne_42_);
lean_dec_ref(v___x_41_);
v_toOne_43_ = lean_ctor_get(v_toAddMonoidWithOne_42_, 2);
lean_inc(v_toOne_43_);
lean_dec_ref(v_toAddMonoidWithOne_42_);
v___f_44_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___redArg___lam__0), 8, 7);
lean_closure_set(v___f_44_, 0, v_u_36_);
lean_closure_set(v___f_44_, 1, v_00_u03c3_37_);
lean_closure_set(v___f_44_, 2, v_a_34_);
lean_closure_set(v___f_44_, 3, v_b_35_);
lean_closure_set(v___f_44_, 4, v_inst_30_);
lean_closure_set(v___f_44_, 5, v_inst_31_);
lean_closure_set(v___f_44_, 6, v_E_33_);
v___x_45_ = l_List_ofFn___redArg(v_t_32_, v___f_44_);
v___x_46_ = l_List_prod___redArg(v_toMul_40_, v_toOne_43_, v___x_45_);
lean_dec(v_toOne_43_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one(lean_object* v_A_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_n_50_, lean_object* v_t_51_, lean_object* v_E_52_, lean_object* v_a_53_, lean_object* v_b_54_, lean_object* v_u_55_, lean_object* v_00_u03c3_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___redArg(v_inst_48_, v_inst_49_, v_t_51_, v_E_52_, v_a_53_, v_b_54_, v_u_55_, v_00_u03c3_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_exchangeTwo__self__eq__one___boxed(lean_object* v_A_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_n_61_, lean_object* v_t_62_, lean_object* v_E_63_, lean_object* v_a_64_, lean_object* v_b_65_, lean_object* v_u_66_, lean_object* v_00_u03c3_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Formalism_REAL_exchangeTwo__self__eq__one(v_A_58_, v_inst_59_, v_inst_60_, v_n_61_, v_t_62_, v_E_63_, v_a_64_, v_b_65_, v_u_66_, v_00_u03c3_67_);
lean_dec(v_n_61_);
return v_res_68_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementE(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
