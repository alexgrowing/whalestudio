// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementB public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_4_ = lp_mathlib_Complex_ofReal(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg(lean_object* v_a_5_, lean_object* v_b_6_, lean_object* v_t_7_, lean_object* v_c_8_, lean_object* v_d_9_){
_start:
{
lean_object* v___y_11_; lean_object* v___y_12_; lean_object* v___y_27_; uint8_t v___x_29_; uint8_t v___x_30_; uint8_t v___x_31_; lean_object* v___y_33_; 
v___x_29_ = lean_nat_dec_eq(v_c_8_, v_d_9_);
v___x_30_ = lean_nat_dec_eq(v_d_9_, v_a_5_);
v___x_31_ = lean_nat_dec_eq(v_c_8_, v_b_6_);
if (v___x_29_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0, &lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0_once, _init_lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0);
v___y_33_ = v___x_34_;
goto v___jp_32_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__1, &lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__1_once, _init_lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__1);
v___y_33_ = v___x_35_;
goto v___jp_32_;
}
v___jp_10_:
{
lean_object* v_re_13_; lean_object* v_im_14_; lean_object* v_re_15_; lean_object* v_im_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_25_; 
v_re_13_ = lean_ctor_get(v___y_11_, 0);
v_im_14_ = lean_ctor_get(v___y_11_, 1);
v_re_15_ = lean_ctor_get(v___y_12_, 0);
v_im_16_ = lean_ctor_get(v___y_12_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v___y_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_18_ = v___y_12_;
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_im_16_);
lean_inc(v_re_15_);
lean_dec(v___y_12_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_23_; 
lean_inc(v_re_13_);
v___f_20_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_20_, 0, v_re_13_);
lean_closure_set(v___f_20_, 1, v_re_15_);
lean_inc(v_im_14_);
v___f_21_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_21_, 0, v_im_14_);
lean_closure_set(v___f_21_, 1, v_im_16_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v___f_21_);
lean_ctor_set(v___x_18_, 0, v___f_20_);
v___x_23_ = v___x_18_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___f_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___f_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
v___jp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0, &lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0_once, _init_lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___closed__0);
v___y_11_ = v___y_27_;
v___y_12_ = v___x_28_;
goto v___jp_10_;
}
v___jp_32_:
{
if (v___x_31_ == 0)
{
lean_dec_ref(v_t_7_);
v___y_27_ = v___y_33_;
goto v___jp_26_;
}
else
{
if (v___x_30_ == 0)
{
lean_dec_ref(v_t_7_);
v___y_27_ = v___y_33_;
goto v___jp_26_;
}
else
{
v___y_11_ = v___y_33_;
v___y_12_ = v_t_7_;
goto v___jp_10_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg___boxed(lean_object* v_a_36_, lean_object* v_b_37_, lean_object* v_t_38_, lean_object* v_c_39_, lean_object* v_d_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg(v_a_36_, v_b_37_, v_t_38_, v_c_39_, v_d_40_);
lean_dec(v_d_40_);
lean_dec(v_c_39_);
lean_dec(v_b_37_);
lean_dec(v_a_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat(lean_object* v_r_42_, lean_object* v_a_43_, lean_object* v_b_44_, lean_object* v_t_45_, lean_object* v_c_46_, lean_object* v_d_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___redArg(v_a_43_, v_b_44_, v_t_45_, v_c_46_, v_d_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat___boxed(lean_object* v_r_49_, lean_object* v_a_50_, lean_object* v_b_51_, lean_object* v_t_52_, lean_object* v_c_53_, lean_object* v_d_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_GradedWeylDivisibility_lfockq__mat(v_r_49_, v_a_50_, v_b_51_, v_t_52_, v_c_53_, v_d_54_);
lean_dec(v_d_54_);
lean_dec(v_c_53_);
lean_dec(v_b_51_);
lean_dec(v_a_50_);
lean_dec(v_r_49_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementB(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
