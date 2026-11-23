// Lean compiler output
// Module: Formalism.IncomingBounds.LevelTail
// Imports: public import Init public meta import Init public import Formalism.IncomingBounds.IncomingBound
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capNat(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_IncomingBounds_uFac___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_IncomingBounds_uFac___closed__0;
static lean_once_cell_t lp_tree_Formalism_IncomingBounds_uFac___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_IncomingBounds_uFac___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_uFac(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_uFac___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capNat___lam__0(lean_object* v_y_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_nat_add(v_y_1_, v_a_2_);
v___x_4_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_3_);
lean_dec(v___x_3_);
v___x_5_ = lp_mathlib_Nat_factorialBinarySplitting(v_a_2_);
v___x_6_ = lean_nat_div(v___x_4_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capNat___lam__0___boxed(lean_object* v_y_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_IncomingBounds_capNat___lam__0(v_y_7_, v_a_8_);
lean_dec(v_a_8_);
lean_dec(v_y_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_capNat(lean_object* v_n0_10_, lean_object* v_y_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_12_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_capNat___lam__0___boxed), 2, 1);
lean_closure_set(v___f_12_, 0, v_y_11_);
v___x_13_ = l_List_range(v_n0_10_);
v___x_14_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_13_, v___f_12_);
return v___x_14_;
}
}
static lean_object* _init_lp_tree_Formalism_IncomingBounds_uFac___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_lp_tree_Formalism_IncomingBounds_uFac___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_obj_once(&lp_tree_Formalism_IncomingBounds_uFac___closed__0, &lp_tree_Formalism_IncomingBounds_uFac___closed__0_once, _init_lp_tree_Formalism_IncomingBounds_uFac___closed__0);
v___x_18_ = l_Rat_neg(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_uFac(lean_object* v_l_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_21_ = lean_obj_once(&lp_tree_Formalism_IncomingBounds_uFac___closed__1, &lp_tree_Formalism_IncomingBounds_uFac___closed__1_once, _init_lp_tree_Formalism_IncomingBounds_uFac___closed__1);
v___x_22_ = l_Rat_pow(v___x_21_, v_x_20_);
v___x_23_ = lean_nat_mul(v_l_19_, v_x_20_);
v___x_24_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_23_);
lean_dec(v___x_23_);
v___x_25_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_24_);
v___x_26_ = l_Rat_mul(v___x_22_, v___x_25_);
lean_dec_ref(v___x_22_);
v___x_27_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_l_19_);
v___x_28_ = l_Rat_pow(v___x_27_, v_x_20_);
v___x_29_ = lp_mathlib_Nat_factorialBinarySplitting(v_x_20_);
v___x_30_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_29_);
v___x_31_ = l_Rat_mul(v___x_28_, v___x_30_);
lean_dec_ref(v___x_28_);
v___x_32_ = l_Rat_div(v___x_26_, v___x_31_);
lean_dec_ref(v___x_26_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_uFac___boxed(lean_object* v_l_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Formalism_IncomingBounds_uFac(v_l_33_, v_x_34_);
lean_dec(v_x_34_);
return v_res_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_IncomingBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_IncomingBounds_LevelTail(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_IncomingBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
