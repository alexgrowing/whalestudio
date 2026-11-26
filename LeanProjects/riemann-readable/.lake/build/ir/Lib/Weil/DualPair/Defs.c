// Lean compiler output
// Module: Lib.Weil.DualPair.Defs
// Imports: public import Init public meta import Init public import Lib.Weil.MixedModel.NamedData
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
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_GRH_New_pairSign___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_homSigns___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_homSigns___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_homSigns___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_homSigns___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_homSigns___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_homSigns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_matrixToVec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_matrixToVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_vecToMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_vecToMatrix___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_vecToMatrix___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_vecToMatrix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_vecToMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_homSigns___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_homSigns___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_homSigns___redArg___closed__0, &lp_GRH_New_homSigns___redArg___closed__0_once, _init_lp_GRH_New_homSigns___redArg___closed__0);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_homSigns___redArg(lean_object* v_s_5_, lean_object* v_s_x27_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&lp_GRH_New_homSigns___redArg___closed__1, &lp_GRH_New_homSigns___redArg___closed__1_once, _init_lp_GRH_New_homSigns___redArg___closed__1);
v___x_9_ = lp_GRH_New_pairSign___redArg(v___x_8_, v_s_x27_6_, v_s_5_, v_i_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_homSigns(lean_object* v_n_10_, lean_object* v_n_x27_11_, lean_object* v_s_12_, lean_object* v_s_x27_13_, lean_object* v_i_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&lp_GRH_New_homSigns___redArg___closed__1, &lp_GRH_New_homSigns___redArg___closed__1_once, _init_lp_GRH_New_homSigns___redArg___closed__1);
v___x_16_ = lp_GRH_New_pairSign___redArg(v___x_15_, v_s_x27_13_, v_s_12_, v_i_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_matrixToVec___redArg(lean_object* v_x_17_, lean_object* v_p_18_){
_start:
{
lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v___x_21_; 
v_fst_19_ = lean_ctor_get(v_p_18_, 0);
lean_inc(v_fst_19_);
v_snd_20_ = lean_ctor_get(v_p_18_, 1);
lean_inc(v_snd_20_);
lean_dec_ref(v_p_18_);
v___x_21_ = lean_apply_2(v_x_17_, v_fst_19_, v_snd_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_matrixToVec(lean_object* v_m_22_, lean_object* v_m_x27_23_, lean_object* v_R_24_, lean_object* v_x_25_, lean_object* v_p_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_GRH_New_matrixToVec___redArg(v_x_25_, v_p_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_vecToMatrix___redArg___lam__0(lean_object* v_y_28_, lean_object* v_i_29_, lean_object* v_j_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v_i_29_);
lean_ctor_set(v___x_31_, 1, v_j_30_);
v___x_32_ = lean_apply_1(v_y_28_, v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_GRH_New_vecToMatrix___redArg___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_mathlib_Equiv_refl___redArg();
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_vecToMatrix___redArg(lean_object* v_y_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_37_; lean_object* v_toFun_38_; lean_object* v___f_39_; lean_object* v___x_40_; 
v___x_37_ = lean_obj_once(&lp_GRH_New_vecToMatrix___redArg___closed__0, &lp_GRH_New_vecToMatrix___redArg___closed__0_once, _init_lp_GRH_New_vecToMatrix___redArg___closed__0);
v_toFun_38_ = lean_ctor_get(v___x_37_, 0);
v___f_39_ = lean_alloc_closure((void*)(lp_GRH_New_vecToMatrix___redArg___lam__0), 3, 1);
lean_closure_set(v___f_39_, 0, v_y_34_);
lean_inc(v_toFun_38_);
v___x_40_ = lean_apply_3(v_toFun_38_, v___f_39_, v_a_35_, v_a_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_vecToMatrix(lean_object* v_m_41_, lean_object* v_m_x27_42_, lean_object* v_R_43_, lean_object* v_y_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_GRH_New_vecToMatrix___redArg(v_y_44_, v_a_45_, v_a_46_);
return v___x_47_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_MixedModel_NamedData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_DualPair_Defs(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_MixedModel_NamedData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
