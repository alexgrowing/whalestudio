// Lean compiler output
// Module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
// Imports: public import Init public meta import Init public import Formalism.GaloisIrreducibility.Statement
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
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_Perm_support(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_Perm_cycleFactorsAux_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_Perm_support___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__1(lean_object*);
static const lean_closure_object lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_List_decidablePerm___redArg(v_inst_1_, v_a_2_, v_b_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__0___boxed(lean_object* v_inst_5_, lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__0(v_inst_5_, v_a_6_, v_b_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__1(lean_object* v_y_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_box(0);
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v_y_10_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_00_u03c3_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc_ref_n(v_inst_15_, 4);
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_17_, 0, v_inst_15_);
v___f_18_ = ((lean_object*)(lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg___closed__0));
lean_inc_n(v_inst_14_, 4);
v___x_19_ = lean_alloc_closure((void*)(lp_mathlib_Equiv_Perm_support), 4, 3);
lean_closure_set(v___x_19_, 0, lean_box(0));
lean_closure_set(v___x_19_, 1, v_inst_15_);
lean_closure_set(v___x_19_, 2, v_inst_14_);
lean_inc_ref_n(v_00_u03c3_16_, 2);
v___x_20_ = lp_mathlib_Equiv_Perm_cycleFactorsAux_go___redArg(v_inst_15_, v_inst_14_, v_00_u03c3_16_, v_inst_14_, v_00_u03c3_16_);
lean_inc_ref_n(v___f_17_, 2);
v___x_21_ = lp_mathlib_Finset_image___redArg(v___f_17_, v___x_19_, v___x_20_);
v___x_22_ = lp_mathlib_Equiv_Perm_support___redArg(v_inst_15_, v_inst_14_, v_00_u03c3_16_);
v___x_23_ = lp_mathlib_Multiset_sub___redArg(v_inst_15_, v_inst_14_, v___x_22_);
v___x_24_ = lp_mathlib_Finset_image___redArg(v___f_17_, v___f_18_, v___x_23_);
v___x_25_ = lp_mathlib_Multiset_ndunion___redArg(v___f_17_, v___x_21_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_00_u03c3_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_tree_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs___redArg(v_inst_27_, v_inst_28_, v_00_u03c3_29_);
return v___x_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
