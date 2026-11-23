// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.LiftLatInst
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.LiftLat public import Formalism.LocalToGlobal.Columns.RowForms public import Formalism.LocalToGlobal.Columns.RowFormsLemmas public import Formalism.LocalToGlobal.Columns.HeckeSp
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
lean_object* lp_tree_Formalism_L2_Col_FormG_incl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_formPts___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_formPts___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_DIV_formPts___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts___redArg(lean_object* v_X_2_, lean_object* v_n_3_, lean_object* v_SG_4_, lean_object* v_00_u039b_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_formPts___redArg___closed__0, &lp_tree_Formalism_L2_DIV_formPts___redArg___closed__0_once, _init_lp_tree_Formalism_L2_DIV_formPts___redArg___closed__0);
v___x_7_ = lp_tree_Formalism_L2_Col_FormG_incl(v_X_2_, v_n_3_, v_SG_4_, v_00_u039b_5_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_6_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts___redArg___boxed(lean_object* v_X_9_, lean_object* v_n_10_, lean_object* v_SG_11_, lean_object* v_00_u039b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_L2_DIV_formPts___redArg(v_X_9_, v_n_10_, v_SG_11_, v_00_u039b_12_);
lean_dec_ref(v_00_u039b_12_);
lean_dec(v_SG_11_);
lean_dec(v_n_10_);
lean_dec_ref(v_X_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts(lean_object* v_X_14_, lean_object* v_n_15_, lean_object* v_ST_16_, lean_object* v_SG_17_, lean_object* v_C_18_, lean_object* v_00_u039b_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_Formalism_L2_DIV_formPts___redArg(v_X_14_, v_n_15_, v_SG_17_, v_00_u039b_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_formPts___boxed(lean_object* v_X_21_, lean_object* v_n_22_, lean_object* v_ST_23_, lean_object* v_SG_24_, lean_object* v_C_25_, lean_object* v_00_u039b_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_L2_DIV_formPts(v_X_21_, v_n_22_, v_ST_23_, v_SG_24_, v_C_25_, v_00_u039b_26_);
lean_dec_ref(v_00_u039b_26_);
lean_dec_ref(v_C_25_);
lean_dec(v_SG_24_);
lean_dec(v_ST_23_);
lean_dec(v_n_22_);
lean_dec_ref(v_X_21_);
return v_res_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLatInst(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
