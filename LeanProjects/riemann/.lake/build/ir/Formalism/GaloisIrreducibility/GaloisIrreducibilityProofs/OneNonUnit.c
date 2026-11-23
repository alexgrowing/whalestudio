// Lean compiler output
// Module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_cons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__0(lean_object* v_toZero_1_, lean_object* v_x_2_){
_start:
{
lean_inc(v_toZero_1_);
return v_toZero_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__0___boxed(lean_object* v_toZero_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__0(v_toZero_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v_toZero_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__1(lean_object* v_M_6_, lean_object* v_toZero_7_, lean_object* v_i_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_apply_1(v_M_6_, v_i_8_);
v___x_11_ = l_Fin_cases___redArg(v_toZero_7_, v___x_10_, v___y_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__1___boxed(lean_object* v_M_12_, lean_object* v_toZero_13_, lean_object* v_i_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__1(v_M_12_, v_toZero_13_, v_i_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec(v_toZero_13_);
return v_res_16_;
}
}
static lean_object* _init_lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___closed__0(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg(lean_object* v_inst_18_, lean_object* v_m_19_, lean_object* v_M_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; lean_object* v_toAddMonoidWithOne_24_; lean_object* v_toOne_25_; lean_object* v_toSemiring_26_; lean_object* v___x_27_; lean_object* v_toZero_28_; lean_object* v___x_29_; lean_object* v_toFun_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
lean_inc_ref(v_inst_18_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_18_);
v_toAddMonoidWithOne_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_toAddMonoidWithOne_24_);
lean_dec_ref(v___x_23_);
v_toOne_25_ = lean_ctor_get(v_toAddMonoidWithOne_24_, 2);
lean_inc(v_toOne_25_);
lean_dec_ref(v_toAddMonoidWithOne_24_);
v_toSemiring_26_ = lean_ctor_get(v_inst_18_, 0);
lean_inc_ref(v_toSemiring_26_);
lean_dec_ref(v_inst_18_);
v___x_27_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_26_);
v_toZero_28_ = lean_ctor_get(v___x_27_, 1);
lean_inc_n(v_toZero_28_, 2);
lean_dec_ref(v___x_27_);
v___x_29_ = lean_obj_once(&lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___closed__0, &lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___closed__0_once, _init_lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___closed__0);
v_toFun_30_ = lean_ctor_get(v___x_29_, 0);
v___f_31_ = lean_alloc_closure((void*)(lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_31_, 0, v_toZero_28_);
v___f_32_ = lean_alloc_closure((void*)(lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_32_, 0, v_M_20_);
lean_closure_set(v___f_32_, 1, v_toZero_28_);
lean_inc(v_m_19_);
v___x_33_ = lean_alloc_closure((void*)(lp_mathlib_Fin_cons___boxed), 5, 4);
lean_closure_set(v___x_33_, 0, v_m_19_);
lean_closure_set(v___x_33_, 1, lean_box(0));
lean_closure_set(v___x_33_, 2, v_toOne_25_);
lean_closure_set(v___x_33_, 3, v___f_31_);
v___x_34_ = lean_alloc_closure((void*)(lp_mathlib_Fin_cons___boxed), 5, 4);
lean_closure_set(v___x_34_, 0, v_m_19_);
lean_closure_set(v___x_34_, 1, lean_box(0));
lean_closure_set(v___x_34_, 2, v___x_33_);
lean_closure_set(v___x_34_, 3, v___f_32_);
lean_inc(v_toFun_30_);
v___x_35_ = lean_apply_3(v_toFun_30_, v___x_34_, v_a_21_, v_a_22_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord(lean_object* v_R_36_, lean_object* v_inst_37_, lean_object* v_m_38_, lean_object* v_M_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_GaloisIrreducibility_BorderedIndexCases_bord___redArg(v_inst_37_, v_m_38_, v_M_39_, v_a_40_, v_a_41_);
return v___x_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit(uint8_t builtin) {
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
