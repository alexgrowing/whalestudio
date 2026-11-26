// Lean compiler output
// Module: New.Spanning.RemainingTerms.LinkVectors
// Imports: public import Init public meta import Init public import New.Spanning.RemainingTerms.Data public import New.Spanning.Unfolding.TermStructure
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
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_GRH_New_framePair___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Filling_lastFramePair___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Filling_lastFramePair___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Filling_lastFramePair___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Filling_lastFramePair___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Matrix_vecEmpty___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Filling_lastFramePair___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Filling_lastFramePair___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastFramePair___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastFramePair(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Filling_zFormIndex___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Filling_zFormIndex___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zFormIndex___lam__0(lean_object*);
static lean_once_cell_t lp_GRH_New_Filling_zFormIndex___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Filling_zFormIndex___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zFormIndex___lam__1(lean_object*);
static const lean_closure_object lp_GRH_New_Filling_zFormIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_zFormIndex___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_zFormIndex___closed__0 = (const lean_object*)&lp_GRH_New_Filling_zFormIndex___closed__0_value;
static const lean_closure_object lp_GRH_New_Filling_zFormIndex___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_zFormIndex___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_zFormIndex___closed__1 = (const lean_object*)&lp_GRH_New_Filling_zFormIndex___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zFormIndex(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastFramePair___redArg(lean_object* v_00_U0001d530_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_T_6_, lean_object* v_k_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_00_u03f1_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_00_u03f1_10_ = lean_ctor_get(v_00_U0001d530_3_, 0);
lean_inc_n(v_00_u03f1_10_, 2);
v___x_11_ = lean_alloc_closure((void*)(lp_GRH_New_framePair___boxed), 8, 6);
lean_closure_set(v___x_11_, 0, lean_box(0));
lean_closure_set(v___x_11_, 1, v_inst_4_);
lean_closure_set(v___x_11_, 2, v_00_U0001d530_3_);
lean_closure_set(v___x_11_, 3, v_inst_5_);
lean_closure_set(v___x_11_, 4, v_T_6_);
lean_closure_set(v___x_11_, 5, v_k_7_);
v___x_12_ = ((lean_object*)(lp_GRH_New_Filling_lastFramePair___redArg___closed__0));
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v_00_u03f1_10_);
v___x_15_ = lean_unsigned_to_nat(0u);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v_00_u03f1_10_);
v___x_17_ = ((lean_object*)(lp_GRH_New_Filling_lastFramePair___redArg___closed__1));
v___x_18_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_18_, 0, lean_box(0));
lean_closure_set(v___x_18_, 1, v___x_15_);
lean_closure_set(v___x_18_, 2, v___x_16_);
lean_closure_set(v___x_18_, 3, v___x_17_);
v___x_19_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_19_, 0, lean_box(0));
lean_closure_set(v___x_19_, 1, v___x_13_);
lean_closure_set(v___x_19_, 2, v___x_14_);
lean_closure_set(v___x_19_, 3, v___x_18_);
v___x_20_ = lp_mathlib_Matrix_submatrix___redArg(v___x_11_, v___x_12_, v___x_19_, v_a_8_, v_a_9_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastFramePair(lean_object* v_00_U0001d530_21_, lean_object* v_R_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_T_25_, lean_object* v_k_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_00_u03f1_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_00_u03f1_29_ = lean_ctor_get(v_00_U0001d530_21_, 0);
lean_inc_n(v_00_u03f1_29_, 2);
v___x_30_ = lean_alloc_closure((void*)(lp_GRH_New_framePair___boxed), 8, 6);
lean_closure_set(v___x_30_, 0, lean_box(0));
lean_closure_set(v___x_30_, 1, v_inst_23_);
lean_closure_set(v___x_30_, 2, v_00_U0001d530_21_);
lean_closure_set(v___x_30_, 3, v_inst_24_);
lean_closure_set(v___x_30_, 4, v_T_25_);
lean_closure_set(v___x_30_, 5, v_k_26_);
v___x_31_ = ((lean_object*)(lp_GRH_New_Filling_lastFramePair___redArg___closed__0));
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_00_u03f1_29_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v_00_u03f1_29_);
v___x_36_ = ((lean_object*)(lp_GRH_New_Filling_lastFramePair___redArg___closed__1));
v___x_37_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_37_, 0, lean_box(0));
lean_closure_set(v___x_37_, 1, v___x_34_);
lean_closure_set(v___x_37_, 2, v___x_35_);
lean_closure_set(v___x_37_, 3, v___x_36_);
v___x_38_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, v___x_32_);
lean_closure_set(v___x_38_, 2, v___x_33_);
lean_closure_set(v___x_38_, 3, v___x_37_);
v___x_39_ = lp_mathlib_Matrix_submatrix___redArg(v___x_30_, v___x_31_, v___x_38_, v_a_27_, v_a_28_);
return v___x_39_;
}
}
static lean_object* _init_lp_GRH_New_Filling_zFormIndex___lam__0___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(2u);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_mod(v___x_41_, v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zFormIndex___lam__0(lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&lp_GRH_New_Filling_zFormIndex___lam__0___closed__0, &lp_GRH_New_Filling_zFormIndex___lam__0___closed__0_once, _init_lp_GRH_New_Filling_zFormIndex___lam__0___closed__0);
return v___x_44_;
}
}
static lean_object* _init_lp_GRH_New_Filling_zFormIndex___lam__1___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_unsigned_to_nat(2u);
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_nat_mod(v___x_46_, v___x_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zFormIndex___lam__1(lean_object* v_x_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_Filling_zFormIndex___lam__1___closed__0, &lp_GRH_New_Filling_zFormIndex___lam__1___closed__0_once, _init_lp_GRH_New_Filling_zFormIndex___lam__1___closed__0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_zFormIndex(lean_object* v_a_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; 
v___f_53_ = ((lean_object*)(lp_GRH_New_Filling_zFormIndex___closed__0));
v___f_54_ = ((lean_object*)(lp_GRH_New_Filling_zFormIndex___closed__1));
v___x_55_ = l_Sum_elim___redArg(v___f_53_, v___f_54_, v_a_52_);
return v___x_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_Data(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_TermStructure(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_LinkVectors(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_RemainingTerms_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_TermStructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
