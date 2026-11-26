// Lean compiler output
// Module: New.Determinant.Exchange.ExplicitMatching
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.Polarisation public import New.Determinant.Exchange.TheoremForPartners public import New.OneLift.ComparisonOperator.DeterminantProducts public import New.OneLift.ComparisonOperator.OneExchange
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
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Complex_instZero;
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__1;
static lean_once_cell_t lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Rows_blockSigns___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Rows_blockSigns___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Rows_blockSigns___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Rows_blockSigns___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Rows_blockSigns___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Rows_blockSigns___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Rows_blockSigns___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Rows_blockSigns___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Rows_blockSigns___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Rows_standardFrame___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__2(lean_object*);
static const lean_closure_object lp_GRH_New_Rows_standardFrame___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Rows_standardFrame___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Rows_standardFrame___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Rows_standardFrame___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Rows_standardFrame___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Rows_standardFrame___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Rows_standardFrame___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Rows_standardFrame___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_Rows_standardFrame___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Rows_standardFrame___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Rows_standardFrame___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0, &lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0);
v___x_4_ = lean_int_neg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__1, &lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__1);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0(lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__2, &lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__2_once, _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__2);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__0___boxed(lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_GRH_New_Rows_blockSigns___redArg___lam__0(v___y_9_);
lean_dec(v___y_9_);
return v_res_10_;
}
}
static lean_object* _init_lp_GRH_New_Rows_blockSigns___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0, &lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Rows_blockSigns___redArg___lam__0___closed__0);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__1(lean_object* v_x_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&lp_GRH_New_Rows_blockSigns___redArg___lam__1___closed__0, &lp_GRH_New_Rows_blockSigns___redArg___lam__1___closed__0_once, _init_lp_GRH_New_Rows_blockSigns___redArg___lam__1___closed__0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg___lam__1___boxed(lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_Rows_blockSigns___redArg___lam__1(v_x_15_);
lean_dec(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns___redArg(lean_object* v_f_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; lean_object* v_toFun_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_21_ = lp_mathlib_Equiv_symm___redArg(v_f_19_);
v_toFun_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_toFun_22_);
lean_dec_ref(v___x_21_);
v___f_23_ = ((lean_object*)(lp_GRH_New_Rows_blockSigns___redArg___closed__0));
v___f_24_ = ((lean_object*)(lp_GRH_New_Rows_blockSigns___redArg___closed__1));
v___x_25_ = lean_apply_1(v_toFun_22_, v_a_20_);
v___x_26_ = l_Sum_elim___redArg(v___f_24_, v___f_23_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_blockSigns(lean_object* v_b_27_, lean_object* v_p_28_, lean_object* v_l_29_, lean_object* v_f_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; lean_object* v_toFun_33_; lean_object* v___f_34_; lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_32_ = lp_mathlib_Equiv_symm___redArg(v_f_30_);
v_toFun_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_toFun_33_);
lean_dec_ref(v___x_32_);
v___f_34_ = ((lean_object*)(lp_GRH_New_Rows_blockSigns___redArg___closed__0));
v___f_35_ = ((lean_object*)(lp_GRH_New_Rows_blockSigns___redArg___closed__1));
v___x_36_ = lean_apply_1(v_toFun_33_, v_a_31_);
v___x_37_ = l_Sum_elim___redArg(v___f_35_, v___f_34_, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_lp_GRH_New_Rows_standardFrame___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_39_ = lp_mathlib_Complex_ofReal(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__0(lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&lp_GRH_New_Rows_standardFrame___redArg___lam__0___closed__0, &lp_GRH_New_Rows_standardFrame___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Rows_standardFrame___redArg___lam__0___closed__0);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__0___boxed(lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_GRH_New_Rows_standardFrame___redArg___lam__0(v_x_42_);
lean_dec(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__1(lean_object* v_e_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_toFun_46_; lean_object* v___x_47_; 
v_toFun_46_ = lean_ctor_get(v_e_44_, 0);
lean_inc(v_toFun_46_);
lean_dec_ref(v_e_44_);
v___x_47_ = lean_apply_1(v_toFun_46_, v___y_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg___lam__2(lean_object* v_val_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v_val_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame___redArg(lean_object* v_inst_53_, lean_object* v_e_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___f_57_ = ((lean_object*)(lp_GRH_New_Rows_standardFrame___redArg___closed__0));
v___f_58_ = lean_alloc_closure((void*)(lp_GRH_New_Rows_standardFrame___redArg___lam__1), 2, 1);
lean_closure_set(v___f_58_, 0, v_e_54_);
v___f_59_ = ((lean_object*)(lp_GRH_New_Rows_standardFrame___redArg___closed__1));
v___x_60_ = lp_mathlib_Complex_instZero;
v___x_61_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_61_, 0, lean_box(0));
lean_closure_set(v___x_61_, 1, lean_box(0));
lean_closure_set(v___x_61_, 2, v_inst_53_);
lean_closure_set(v___x_61_, 3, v___x_60_);
lean_closure_set(v___x_61_, 4, v___f_57_);
v___x_62_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_62_, 0, lean_box(0));
lean_closure_set(v___x_62_, 1, lean_box(0));
lean_closure_set(v___x_62_, 2, lean_box(0));
lean_closure_set(v___x_62_, 3, v___f_58_);
lean_closure_set(v___x_62_, 4, v___f_59_);
v___x_63_ = ((lean_object*)(lp_GRH_New_Rows_standardFrame___redArg___closed__2));
v___x_64_ = lp_mathlib_Matrix_submatrix___redArg(v___x_61_, v___x_62_, v___x_63_, v_a_55_, v_a_56_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_standardFrame(lean_object* v_m_65_, lean_object* v_a_66_, lean_object* v_p_67_, lean_object* v_inst_68_, lean_object* v_e_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_GRH_New_Rows_standardFrame___redArg(v_inst_68_, v_e_69_, v_a_70_, v_a_71_);
return v___x_72_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_Polarisation(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Exchange_TheoremForPartners(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_DeterminantProducts(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_OneExchange(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_Exchange_ExplicitMatching(uint8_t builtin) {
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
res = initialize_GRH_Lib_GLn_SchurModule_Polarisation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Exchange_TheoremForPartners(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_DeterminantProducts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_OneExchange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
