// Lean compiler output
// Module: Formalism.LocalRingCardinality.SpanPowerMembership.Primes
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.CyclotomicNorms.StatementI
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
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_List_prod___at___00Nat_equivProdNatFactoredNumbers_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_Examples_u2082_prodPowSubOne_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_Examples_u2082_prodPowSubOne_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_Examples_u2082_prodPowSubOne_spec__0(lean_object* v_g_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
v___x_4_ = l_List_reverse___redArg(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_18_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_18_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_18_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_head_5_, v___x_10_);
lean_dec(v_head_5_);
v___x_12_ = lean_nat_pow(v_g_1_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_nat_sub(v___x_12_, v___x_10_);
lean_dec(v___x_12_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_a_3_);
lean_ctor_set(v___x_8_, 0, v___x_13_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_a_3_);
v___x_15_ = v_reuseFailAlloc_17_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_15_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_Examples_u2082_prodPowSubOne_spec__0___boxed(lean_object* v_g_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_Examples_u2082_prodPowSubOne_spec__0(v_g_19_, v_a_20_, v_a_21_);
lean_dec(v_g_19_);
return v_res_22_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(9u);
v___x_24_ = l_List_range(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne(lean_object* v_g_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_26_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___closed__0, &lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___closed__0_once, _init_lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___closed__0);
v___x_27_ = lean_box(0);
v___x_28_ = lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_Examples_u2082_prodPowSubOne_spec__0(v_g_25_, v___x_26_, v___x_27_);
v___x_29_ = lp_mathlib_List_prod___at___00Nat_equivProdNatFactoredNumbers_spec__1(v___x_28_);
lean_dec(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne___boxed(lean_object* v_g_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_BasicNotions_Examples_u2082_prodPowSubOne(v_g_30_);
lean_dec(v_g_30_);
return v_res_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Primes(uint8_t builtin) {
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
res = initialize_tree_Formalism_CyclotomicNorms_StatementI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
