// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.BranchSandwichDivisors.StatementL public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean public import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut public import Formalism.HarderNarasimhan.ShiftInvariance
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
lean_object* lp_mathlib_LinearMap_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg___lam__0(lean_object* v_x_1_, lean_object* v_i_2_, lean_object* v_inst_3_, lean_object* v_c_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_apply_2(v_x_1_, v_i_2_, v___y_5_);
v___x_7_ = lean_apply_2(v_inst_3_, v_c_4_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg___lam__1(lean_object* v_x_8_, lean_object* v_inst_9_, lean_object* v_c_10_, lean_object* v_i_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_i_11_);
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg___lam__0), 5, 4);
lean_closure_set(v___f_13_, 0, v_x_8_);
lean_closure_set(v___f_13_, 1, v_i_11_);
lean_closure_set(v___f_13_, 2, v_inst_9_);
lean_closure_set(v___f_13_, 3, v_c_10_);
v___x_14_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_14_, 0, lean_box(0));
lean_closure_set(v___x_14_, 1, lean_box(0));
lean_closure_set(v___x_14_, 2, v_i_11_);
v___x_15_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___x_14_, v___f_13_, v___y_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg(lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_c_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_toAddMonoid_21_; lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_toAddMonoid_21_ = lean_ctor_get(v_inst_16_, 0);
lean_inc_ref(v_toAddMonoid_21_);
lean_dec_ref(v_inst_16_);
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_22_, 0, v_x_20_);
lean_closure_set(v___f_22_, 1, v_inst_17_);
lean_closure_set(v___f_22_, 2, v_c_19_);
v___x_23_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_21_);
v___x_24_ = l_List_finRange(v_n_18_);
v___x_25_ = lp_mathlib_Finset_sum___redArg(v___x_23_, v___x_24_, v___f_22_);
lean_dec_ref(v___x_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap(lean_object* v_K_26_, lean_object* v_inst_27_, lean_object* v_V_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_n_31_, lean_object* v_c_32_, lean_object* v_x_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___redArg(v_inst_29_, v_inst_30_, v_n_31_, v_c_32_, v_x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap___boxed(lean_object* v_K_35_, lean_object* v_inst_36_, lean_object* v_V_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_n_40_, lean_object* v_c_41_, lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap(v_K_35_, v_inst_36_, v_V_37_, v_inst_38_, v_inst_39_, v_n_40_, v_c_41_, v_x_42_);
lean_dec_ref(v_inst_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___redArg___lam__0(lean_object* v_x_44_, lean_object* v_inst_45_, lean_object* v_c_46_, lean_object* v_i_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_apply_2(v_x_44_, v_i_47_, v___y_48_);
v___x_50_ = lean_apply_2(v_inst_45_, v_c_46_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___redArg(lean_object* v_inst_51_, lean_object* v_c_52_, lean_object* v_x_53_){
_start:
{
lean_object* v___f_54_; lean_object* v___f_55_; 
v___f_54_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___redArg___lam__0), 5, 3);
lean_closure_set(v___f_54_, 0, v_x_53_);
lean_closure_set(v___f_54_, 1, v_inst_51_);
lean_closure_set(v___f_54_, 2, v_c_52_);
v___f_55_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_55_, 0, v___f_54_);
return v___f_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap(lean_object* v_K_56_, lean_object* v_inst_57_, lean_object* v_V_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_n_61_, lean_object* v_c_62_, lean_object* v_x_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___redArg(v_inst_60_, v_c_62_, v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap___boxed(lean_object* v_K_65_, lean_object* v_inst_66_, lean_object* v_V_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_c_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_tree_Formalism_BranchingDeterminantCap_PrismTransfer_colMap(v_K_65_, v_inst_66_, v_V_67_, v_inst_68_, v_inst_69_, v_n_70_, v_c_71_, v_x_72_);
lean_dec(v_n_70_);
lean_dec_ref(v_inst_68_);
lean_dec_ref(v_inst_66_);
return v_res_73_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementL(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean(uint8_t builtin);
lean_object* initialize_tree_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer(uint8_t builtin) {
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
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
