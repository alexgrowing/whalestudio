// Lean compiler output
// Module: New.Appendix.DiscreteSeries.Localization
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability public import New.Appendix.DiscreteSeries.SteepParameters
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__1 = (const lean_object*)&lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__1(lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_onBlock___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_onBlock___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___closed__0, &lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___closed__0_once, _init_lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__0(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1(lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___closed__0, &lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___closed__0_once, _init_lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1___boxed(lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___lam__1(v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg(lean_object* v_e_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___x_17_; lean_object* v_toFun_18_; lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = lp_mathlib_Equiv_symm___redArg(v_e_15_);
v_toFun_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_toFun_18_);
lean_dec_ref(v___x_17_);
v___f_19_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__0));
v___f_20_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg___closed__1));
v___x_21_ = lean_apply_1(v_toFun_18_, v_i_16_);
v___x_22_ = l_Sum_elim___redArg(v___f_19_, v___f_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator(lean_object* v_n_23_, lean_object* v_X_24_, lean_object* v_M_25_, lean_object* v_e_26_, lean_object* v_i_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GRH_New_DiscreteSeries_offBlockIndicator___redArg(v_e_26_, v_i_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_offBlockIndicator___boxed(lean_object* v_n_29_, lean_object* v_X_30_, lean_object* v_M_31_, lean_object* v_e_32_, lean_object* v_i_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_DiscreteSeries_offBlockIndicator(v_n_29_, v_X_30_, v_M_31_, v_e_32_, v_i_33_);
lean_dec(v_M_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__0(lean_object* v_e_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_toFun_37_; lean_object* v___x_38_; 
v_toFun_37_ = lean_ctor_get(v_e_35_, 0);
lean_inc(v_toFun_37_);
lean_dec_ref(v_e_35_);
v___x_38_ = lean_apply_1(v_toFun_37_, v___y_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__1(lean_object* v_val_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v_val_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___redArg(lean_object* v_e_42_, lean_object* v_A_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___f_46_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__0), 2, 1);
lean_closure_set(v___f_46_, 0, v_e_42_);
v___f_47_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_onBlock___redArg___closed__0));
v___x_48_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_48_, 0, lean_box(0));
lean_closure_set(v___x_48_, 1, lean_box(0));
lean_closure_set(v___x_48_, 2, lean_box(0));
lean_closure_set(v___x_48_, 3, v___f_46_);
lean_closure_set(v___x_48_, 4, v___f_47_);
lean_inc_ref(v___x_48_);
v___x_49_ = lp_mathlib_Matrix_submatrix___redArg(v_A_43_, v___x_48_, v___x_48_, v_a_44_, v_a_45_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock(lean_object* v_n_50_, lean_object* v_X_51_, lean_object* v_M_52_, lean_object* v_e_53_, lean_object* v_A_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_57_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_onBlock___redArg___lam__0), 2, 1);
lean_closure_set(v___f_57_, 0, v_e_53_);
v___f_58_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_onBlock___redArg___closed__0));
v___x_59_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_59_, 0, lean_box(0));
lean_closure_set(v___x_59_, 1, lean_box(0));
lean_closure_set(v___x_59_, 2, lean_box(0));
lean_closure_set(v___x_59_, 3, v___f_57_);
lean_closure_set(v___x_59_, 4, v___f_58_);
lean_inc_ref(v___x_59_);
v___x_60_ = lp_mathlib_Matrix_submatrix___redArg(v_A_54_, v___x_59_, v___x_59_, v_a_55_, v_a_56_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_onBlock___boxed(lean_object* v_n_61_, lean_object* v_X_62_, lean_object* v_M_63_, lean_object* v_e_64_, lean_object* v_A_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_GRH_New_DiscreteSeries_onBlock(v_n_61_, v_X_62_, v_M_63_, v_e_64_, v_A_65_, v_a_66_, v_a_67_);
lean_dec(v_M_63_);
return v_res_68_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_SquareIntegrability(uint8_t builtin);
lean_object* initialize_GRH_New_Appendix_DiscreteSeries_SteepParameters(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Appendix_DiscreteSeries_Localization(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_SquareIntegrability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Appendix_DiscreteSeries_SteepParameters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
