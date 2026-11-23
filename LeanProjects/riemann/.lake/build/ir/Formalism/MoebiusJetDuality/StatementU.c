// Lean compiler output
// Module: Formalism.MoebiusJetDuality.StatementU
// Imports: public import Init public meta import Init public import Formalism.MoebiusJetDuality.StatementV public import Formalism.SatakeDualWeyl.Statement
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MJ_blk___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MJ_blk___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MJ_blk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MJ_blk___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MJ_blk___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MJ_blk___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_vecOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_vecOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_vecOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_MJ_blk___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___redArg___lam__0(lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_MJ_blk___redArg___lam__0___closed__0, &lp_tree_Formalism_MJ_blk___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_MJ_blk___redArg___lam__0___closed__0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___redArg___lam__0___boxed(lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_MJ_blk___redArg___lam__0(v___y_6_, v___y_7_);
lean_dec(v___y_7_);
lean_dec(v___y_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___redArg(lean_object* v_A_10_, lean_object* v_D_11_){
_start:
{
lean_object* v_val_12_; lean_object* v_inv_13_; lean_object* v_val_14_; lean_object* v_inv_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_25_; 
v_val_12_ = lean_ctor_get(v_A_10_, 0);
lean_inc(v_val_12_);
v_inv_13_ = lean_ctor_get(v_A_10_, 1);
lean_inc(v_inv_13_);
lean_dec_ref(v_A_10_);
v_val_14_ = lean_ctor_get(v_D_11_, 0);
v_inv_15_ = lean_ctor_get(v_D_11_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_D_11_);
if (v_isSharedCheck_25_ == 0)
{
v___x_17_ = v_D_11_;
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_inv_15_);
lean_inc(v_val_14_);
lean_dec(v_D_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
v___f_19_ = ((lean_object*)(lp_tree_Formalism_MJ_blk___redArg___closed__0));
v___x_20_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_20_, 0, lean_box(0));
lean_closure_set(v___x_20_, 1, lean_box(0));
lean_closure_set(v___x_20_, 2, lean_box(0));
lean_closure_set(v___x_20_, 3, lean_box(0));
lean_closure_set(v___x_20_, 4, lean_box(0));
lean_closure_set(v___x_20_, 5, v_val_12_);
lean_closure_set(v___x_20_, 6, v___f_19_);
lean_closure_set(v___x_20_, 7, v___f_19_);
lean_closure_set(v___x_20_, 8, v_val_14_);
v___x_21_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_21_, 0, lean_box(0));
lean_closure_set(v___x_21_, 1, lean_box(0));
lean_closure_set(v___x_21_, 2, lean_box(0));
lean_closure_set(v___x_21_, 3, lean_box(0));
lean_closure_set(v___x_21_, 4, lean_box(0));
lean_closure_set(v___x_21_, 5, v_inv_13_);
lean_closure_set(v___x_21_, 6, v___f_19_);
lean_closure_set(v___x_21_, 7, v___f_19_);
lean_closure_set(v___x_21_, 8, v_inv_15_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_21_);
lean_ctor_set(v___x_17_, 0, v___x_20_);
v___x_23_ = v___x_17_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk(lean_object* v_p_26_, lean_object* v_q_27_, lean_object* v_A_28_, lean_object* v_D_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_tree_Formalism_MJ_blk___redArg(v_A_28_, v_D_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_blk___boxed(lean_object* v_p_31_, lean_object* v_q_32_, lean_object* v_A_33_, lean_object* v_D_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Formalism_MJ_blk(v_p_31_, v_q_32_, v_A_33_, v_D_34_);
lean_dec(v_q_32_);
lean_dec(v_p_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_vecOf___redArg(lean_object* v_z_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_fst_38_; lean_object* v_snd_39_; lean_object* v___x_40_; 
v_fst_38_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_fst_38_);
v_snd_39_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_snd_39_);
lean_dec_ref(v_x_37_);
v___x_40_ = lean_apply_2(v_z_36_, v_fst_38_, v_snd_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_vecOf(lean_object* v_p_41_, lean_object* v_q_42_, lean_object* v_z_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_tree_Formalism_MJ_vecOf___redArg(v_z_43_, v_x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_vecOf___boxed(lean_object* v_p_46_, lean_object* v_q_47_, lean_object* v_z_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_MJ_vecOf(v_p_46_, v_q_47_, v_z_48_, v_x_49_);
lean_dec(v_q_47_);
lean_dec(v_p_46_);
return v_res_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_MoebiusJetDuality_StatementV(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_MoebiusJetDuality_StatementU(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MoebiusJetDuality_StatementV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
