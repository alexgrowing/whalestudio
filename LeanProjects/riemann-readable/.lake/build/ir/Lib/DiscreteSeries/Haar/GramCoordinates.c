// Lean compiler output
// Module: Lib.DiscreteSeries.Haar.GramCoordinates
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Haar.CayleyChart
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
lean_object* lp_mathlib_Equiv_piUnique___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Homeomorph_piCongrRight___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_submatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_joinCols___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_joinCols___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_joinCols___redArg___closed__0 = (const lean_object*)&lp_GRH_New_joinCols___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_toCol___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_toCol___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_toCol___redArg___closed__0 = (const lean_object*)&lp_GRH_New_toCol___redArg___closed__0_value;
static lean_once_cell_t lp_GRH_New_toCol___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_toCol___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_toCol___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_toCol___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_toCol(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__0(lean_object* v___y_1_){
_start:
{
lean_inc(v___y_1_);
return v___y_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__0___boxed(lean_object* v___y_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_GRH_New_joinCols___redArg___lam__0(v___y_2_);
lean_dec(v___y_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__1(lean_object* v___x_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_toFun_6_; lean_object* v___x_7_; 
v_toFun_6_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toFun_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lean_apply_1(v_toFun_6_, v___y_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__2(lean_object* v_e_8_, lean_object* v___f_9_, lean_object* v_p_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_fst_13_; lean_object* v_snd_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___f_17_; lean_object* v___x_18_; 
v_fst_13_ = lean_ctor_get(v_p_10_, 0);
lean_inc(v_fst_13_);
v_snd_14_ = lean_ctor_get(v_p_10_, 1);
lean_inc(v_snd_14_);
lean_dec_ref(v_p_10_);
v___x_15_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromCols), 8, 6);
lean_closure_set(v___x_15_, 0, lean_box(0));
lean_closure_set(v___x_15_, 1, lean_box(0));
lean_closure_set(v___x_15_, 2, lean_box(0));
lean_closure_set(v___x_15_, 3, lean_box(0));
lean_closure_set(v___x_15_, 4, v_fst_13_);
lean_closure_set(v___x_15_, 5, v_snd_14_);
v___x_16_ = lp_mathlib_Equiv_symm___redArg(v_e_8_);
v___f_17_ = lean_alloc_closure((void*)(lp_GRH_New_joinCols___redArg___lam__1), 2, 1);
lean_closure_set(v___f_17_, 0, v___x_16_);
v___x_18_ = lp_mathlib_Matrix_submatrix___redArg(v___x_15_, v___f_9_, v___f_17_, v___y_11_, v___y_12_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__3(lean_object* v_e_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_toFun_21_; lean_object* v___x_22_; 
v_toFun_21_ = lean_ctor_get(v_e_19_, 0);
lean_inc(v_toFun_21_);
lean_dec_ref(v_e_19_);
v___x_22_ = lean_apply_1(v_toFun_21_, v___y_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__5(lean_object* v___f_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___y_24_);
v___x_26_ = lean_apply_1(v___f_23_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__4(lean_object* v___f_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v___y_28_);
v___x_30_ = lean_apply_1(v___f_27_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg___lam__6(lean_object* v___f_31_, lean_object* v___f_32_, lean_object* v___f_33_, lean_object* v_Y_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_inc(v___f_31_);
lean_inc_ref(v_Y_34_);
v___x_35_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_35_, 0, lean_box(0));
lean_closure_set(v___x_35_, 1, lean_box(0));
lean_closure_set(v___x_35_, 2, lean_box(0));
lean_closure_set(v___x_35_, 3, lean_box(0));
lean_closure_set(v___x_35_, 4, lean_box(0));
lean_closure_set(v___x_35_, 5, v_Y_34_);
lean_closure_set(v___x_35_, 6, v___f_31_);
lean_closure_set(v___x_35_, 7, v___f_32_);
v___x_36_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, lean_box(0));
lean_closure_set(v___x_36_, 3, lean_box(0));
lean_closure_set(v___x_36_, 4, lean_box(0));
lean_closure_set(v___x_36_, 5, v_Y_34_);
lean_closure_set(v___x_36_, 6, v___f_31_);
lean_closure_set(v___x_36_, 7, v___f_33_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols___redArg(lean_object* v_e_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___x_46_; 
v___f_40_ = ((lean_object*)(lp_GRH_New_joinCols___redArg___closed__0));
lean_inc_ref(v_e_39_);
v___f_41_ = lean_alloc_closure((void*)(lp_GRH_New_joinCols___redArg___lam__2), 5, 2);
lean_closure_set(v___f_41_, 0, v_e_39_);
lean_closure_set(v___f_41_, 1, v___f_40_);
v___f_42_ = lean_alloc_closure((void*)(lp_GRH_New_joinCols___redArg___lam__3), 2, 1);
lean_closure_set(v___f_42_, 0, v_e_39_);
lean_inc_ref(v___f_42_);
v___f_43_ = lean_alloc_closure((void*)(lp_GRH_New_joinCols___redArg___lam__5), 2, 1);
lean_closure_set(v___f_43_, 0, v___f_42_);
v___f_44_ = lean_alloc_closure((void*)(lp_GRH_New_joinCols___redArg___lam__4), 2, 1);
lean_closure_set(v___f_44_, 0, v___f_42_);
v___f_45_ = lean_alloc_closure((void*)(lp_GRH_New_joinCols___redArg___lam__6), 4, 3);
lean_closure_set(v___f_45_, 0, v___f_40_);
lean_closure_set(v___f_45_, 1, v___f_43_);
lean_closure_set(v___f_45_, 2, v___f_44_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___f_41_);
lean_ctor_set(v___x_46_, 1, v___f_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_joinCols(lean_object* v_00_u03b9_47_, lean_object* v_n_48_, lean_object* v_n_u2081_49_, lean_object* v_n_u2082_50_, lean_object* v_e_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_GRH_New_joinCols___redArg(v_e_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg___lam__0(lean_object* v___x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lp_mathlib_Equiv_piUnique___redArg(v___x_53_);
v___x_56_ = lp_mathlib_Equiv_symm___redArg(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg___lam__0___boxed(lean_object* v___x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_GRH_New_toCol___redArg___lam__0(v___x_57_, v_x_58_);
lean_dec(v_x_58_);
return v_res_59_;
}
}
static lean_object* _init_lp_GRH_New_toCol___redArg___closed__1(void){
_start:
{
lean_object* v___f_62_; lean_object* v___x_63_; 
v___f_62_ = ((lean_object*)(lp_GRH_New_toCol___redArg___closed__0));
v___x_63_ = lp_mathlib_Homeomorph_piCongrRight___redArg(v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg(){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&lp_GRH_New_toCol___redArg___closed__1, &lp_GRH_New_toCol___redArg___closed__1_once, _init_lp_GRH_New_toCol___redArg___closed__1);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toCol___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_GRH_New_toCol___redArg();
return v_res_67_;
}
}
static lean_object* _init_lp_GRH_New_toCol___closed__0(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_GRH_New_toCol___redArg();
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toCol(lean_object* v_00_u03ba_69_, lean_object* v_R_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&lp_GRH_New_toCol___closed__0, &lp_GRH_New_toCol___closed__0_once, _init_lp_GRH_New_toCol___closed__0);
return v___x_72_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Haar_CayleyChart(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Haar_GramCoordinates(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Haar_CayleyChart(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
