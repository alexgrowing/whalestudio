// Lean compiler output
// Module: Formalism.FormalDegreeBessel.StatementDS
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_prod___at___00Formalism_REAL_vand_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_capP___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_capP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_QuantumDeterminants_epsHol(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_epsHol___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_QuantumDeterminants_ncBetween___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_ncBetween___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_ncBetween(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_capP___lam__0(lean_object* v_Y_1_, lean_object* v_lam_2_, lean_object* v_s_3_){
_start:
{
lean_object* v_re_4_; lean_object* v_im_5_; lean_object* v___x_6_; lean_object* v_re_7_; lean_object* v_im_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_17_; 
v_re_4_ = lean_ctor_get(v_Y_1_, 0);
lean_inc(v_re_4_);
v_im_5_ = lean_ctor_get(v_Y_1_, 1);
lean_inc(v_im_5_);
lean_dec_ref(v_Y_1_);
v___x_6_ = lean_apply_1(v_lam_2_, v_s_3_);
v_re_7_ = lean_ctor_get(v___x_6_, 0);
v_im_8_ = lean_ctor_get(v___x_6_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_17_ == 0)
{
v___x_10_ = v___x_6_;
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_im_8_);
lean_inc(v_re_7_);
lean_dec(v___x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___x_15_; 
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v_re_4_);
lean_closure_set(v___f_12_, 1, v_re_7_);
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_13_, 0, v_im_5_);
lean_closure_set(v___f_13_, 1, v_im_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___f_13_);
lean_ctor_set(v___x_10_, 0, v___f_12_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___f_12_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___f_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_capP(lean_object* v_n_18_, lean_object* v_lam_19_, lean_object* v_Y_20_){
_start:
{
lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Formalism_QuantumDeterminants_capP___lam__0), 3, 2);
lean_closure_set(v___f_21_, 0, v_Y_20_);
lean_closure_set(v___f_21_, 1, v_lam_19_);
v___x_22_ = l_List_finRange(v_n_18_);
v___x_23_ = lp_tree_Finset_prod___at___00Formalism_REAL_vand_spec__1___redArg(v___x_22_, v___f_21_);
return v___x_23_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_QuantumDeterminants_epsHol(lean_object* v_n_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_n_24_, v___x_26_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_mod(v___x_28_, v___x_27_);
lean_dec(v___x_27_);
v___x_30_ = lean_nat_dec_eq(v_i_25_, v___x_29_);
lean_dec(v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; 
v___x_31_ = 1;
return v___x_31_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 0;
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_epsHol___boxed(lean_object* v_n_33_, lean_object* v_i_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = lp_tree_Formalism_QuantumDeterminants_epsHol(v_n_33_, v_i_34_);
lean_dec(v_i_34_);
lean_dec(v_n_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_QuantumDeterminants_ncBetween___lam__0(lean_object* v_a_37_, lean_object* v_b_38_, lean_object* v_00_u03b5_39_, lean_object* v_a_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = lean_nat_dec_lt(v_a_37_, v_a_40_);
if (v___x_41_ == 0)
{
lean_dec(v_a_40_);
lean_dec_ref(v_00_u03b5_39_);
lean_dec(v_a_37_);
return v___x_41_;
}
else
{
uint8_t v___x_42_; uint8_t v___y_44_; 
v___x_42_ = lean_nat_dec_lt(v_a_40_, v_b_38_);
if (v___x_42_ == 0)
{
lean_dec(v_a_40_);
lean_dec_ref(v_00_u03b5_39_);
lean_dec(v_a_37_);
return v___x_42_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
lean_inc_ref(v_00_u03b5_39_);
v___x_46_ = lean_apply_1(v_00_u03b5_39_, v_a_40_);
v___x_47_ = lean_apply_1(v_00_u03b5_39_, v_a_37_);
v___x_48_ = lean_unbox(v___x_46_);
if (v___x_48_ == 0)
{
uint8_t v___x_49_; 
v___x_49_ = lean_unbox(v___x_47_);
if (v___x_49_ == 0)
{
v___y_44_ = v___x_42_;
goto v___jp_43_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = lean_unbox(v___x_47_);
return v___x_50_;
}
}
else
{
uint8_t v___x_51_; 
v___x_51_ = lean_unbox(v___x_47_);
v___y_44_ = v___x_51_;
goto v___jp_43_;
}
}
v___jp_43_:
{
if (v___y_44_ == 0)
{
return v___x_42_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_ncBetween___lam__0___boxed(lean_object* v_a_52_, lean_object* v_b_53_, lean_object* v_00_u03b5_54_, lean_object* v_a_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = lp_tree_Formalism_QuantumDeterminants_ncBetween___lam__0(v_a_52_, v_b_53_, v_00_u03b5_54_, v_a_55_);
lean_dec(v_b_53_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_QuantumDeterminants_ncBetween(lean_object* v_n_58_, lean_object* v_00_u03b5_59_, lean_object* v_a_60_, lean_object* v_b_61_){
_start:
{
lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___f_62_ = lean_alloc_closure((void*)(lp_tree_Formalism_QuantumDeterminants_ncBetween___lam__0___boxed), 4, 3);
lean_closure_set(v___f_62_, 0, v_a_60_);
lean_closure_set(v___f_62_, 1, v_b_61_);
lean_closure_set(v___f_62_, 2, v_00_u03b5_59_);
v___x_63_ = l_List_finRange(v_n_58_);
v___x_64_ = lp_mathlib_Multiset_filter___redArg(v___f_62_, v___x_63_);
v___x_65_ = l_List_lengthTR___redArg(v___x_64_);
lean_dec(v___x_64_);
return v___x_65_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementE(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FormalDegreeBessel_StatementDS(uint8_t builtin) {
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
