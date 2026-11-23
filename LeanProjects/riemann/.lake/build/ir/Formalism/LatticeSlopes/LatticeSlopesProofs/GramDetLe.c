// Lean compiler output
// Module: Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
// Imports: public import Init public meta import Init public import Formalism.LatticeSlopes.Statement
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
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg___lam__0(lean_object* v_c_1_, lean_object* v_v_2_, lean_object* v_toNormedSpace_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_i_4_);
v___x_5_ = lean_apply_1(v_c_1_, v_i_4_);
v___x_6_ = lean_apply_1(v_v_2_, v_i_4_);
v___x_7_ = lean_apply_2(v_toNormedSpace_3_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg___lam__1(lean_object* v_v_8_, lean_object* v_toNormedSpace_9_, lean_object* v_toAddMonoid_10_, lean_object* v_inst_11_, lean_object* v_c_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; 
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_F_linearCombinationMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_13_, 0, v_c_12_);
lean_closure_set(v___f_13_, 1, v_v_8_);
lean_closure_set(v___f_13_, 2, v_toNormedSpace_9_);
v___x_14_ = lp_mathlib_Finset_sum___redArg(v_toAddMonoid_10_, v_inst_11_, v___f_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg___lam__1___boxed(lean_object* v_v_15_, lean_object* v_toNormedSpace_16_, lean_object* v_toAddMonoid_17_, lean_object* v_inst_18_, lean_object* v_c_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_F_linearCombinationMap___redArg___lam__1(v_v_15_, v_toNormedSpace_16_, v_toAddMonoid_17_, v_inst_18_, v_c_19_);
lean_dec_ref(v_toAddMonoid_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap___redArg(lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_v_24_){
_start:
{
lean_object* v_toAddCommGroup_25_; lean_object* v_toAddMonoid_26_; lean_object* v_toNormedSpace_27_; lean_object* v___f_28_; 
v_toAddCommGroup_25_ = lean_ctor_get(v_inst_21_, 1);
lean_inc_ref(v_toAddCommGroup_25_);
lean_dec_ref(v_inst_21_);
v_toAddMonoid_26_ = lean_ctor_get(v_toAddCommGroup_25_, 0);
lean_inc_ref(v_toAddMonoid_26_);
lean_dec_ref(v_toAddCommGroup_25_);
v_toNormedSpace_27_ = lean_ctor_get(v_inst_22_, 0);
lean_inc(v_toNormedSpace_27_);
lean_dec_ref(v_inst_22_);
v___f_28_ = lean_alloc_closure((void*)(lp_tree_Formalism_F_linearCombinationMap___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_28_, 0, v_v_24_);
lean_closure_set(v___f_28_, 1, v_toNormedSpace_27_);
lean_closure_set(v___f_28_, 2, v_toAddMonoid_26_);
lean_closure_set(v___f_28_, 3, v_inst_23_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_F_linearCombinationMap(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_00_u03b9_32_, lean_object* v_inst_33_, lean_object* v_v_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_tree_Formalism_F_linearCombinationMap___redArg(v_inst_30_, v_inst_31_, v_inst_33_, v_v_34_);
return v___x_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
