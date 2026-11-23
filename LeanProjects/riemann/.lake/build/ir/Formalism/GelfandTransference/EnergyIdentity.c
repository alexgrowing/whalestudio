// Lean compiler output
// Module: Formalism.GelfandTransference.EnergyIdentity
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__0(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_qbinom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_qbinom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_zdual(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_zdual___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__0(lean_object* v_u_1_, lean_object* v_j_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_apply_1(v_u_1_, v_j_2_);
v___x_4_ = lean_nat_to_int(v___x_3_);
v___x_5_ = lean_unsigned_to_nat(2u);
v___x_6_ = l_Int_pow(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__1(lean_object* v_j_9_, lean_object* v_u_10_, lean_object* v_i_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_add(v_i_11_, v___x_12_);
v___x_14_ = lean_nat_dec_eq(v___x_13_, v_j_9_);
lean_dec(v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec(v_i_11_);
lean_dec_ref(v_u_10_);
lean_dec(v_j_9_);
v___x_15_ = lean_obj_once(&lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0, &lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0_once, _init_lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc_ref(v_u_10_);
v___x_16_ = lean_apply_1(v_u_10_, v_i_11_);
v___x_17_ = lean_nat_to_int(v___x_16_);
v___x_18_ = lean_apply_1(v_u_10_, v_j_9_);
v___x_19_ = lean_nat_to_int(v___x_18_);
v___x_20_ = lean_int_mul(v___x_17_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_17_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0(lean_object* v_s_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0___closed__0));
v___x_24_ = lean_obj_once(&lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0, &lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0_once, _init_lp_tree_Formalism_HadamardInequality_energy___lam__1___closed__0);
v___x_25_ = l_List_foldrTR___redArg(v___f_23_, v___x_24_, v_s_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(lean_object* v_s_26_, lean_object* v_f_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lp_mathlib_Multiset_map___redArg(v_f_27_, v_s_26_);
v___x_29_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0_spec__0(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy___lam__2(lean_object* v_u_30_, lean_object* v___x_31_, lean_object* v_j_32_){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; 
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_HadamardInequality_energy___lam__1), 3, 2);
lean_closure_set(v___f_33_, 0, v_j_32_);
lean_closure_set(v___f_33_, 1, v_u_30_);
v___x_34_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_31_, v___f_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_energy(lean_object* v_m_35_, lean_object* v_u_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc_ref(v_u_36_);
v___f_37_ = lean_alloc_closure((void*)(lp_tree_Formalism_HadamardInequality_energy___lam__0), 2, 1);
lean_closure_set(v___f_37_, 0, v_u_36_);
v___x_38_ = l_List_finRange(v_m_35_);
lean_inc_n(v___x_38_, 2);
v___f_39_ = lean_alloc_closure((void*)(lp_tree_Formalism_HadamardInequality_energy___lam__2), 3, 2);
lean_closure_set(v___f_39_, 0, v_u_36_);
lean_closure_set(v___f_39_, 1, v___x_38_);
v___x_40_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_38_, v___f_37_);
v___x_41_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_38_, v___f_39_);
v___x_42_ = lean_int_sub(v___x_40_, v___x_41_);
lean_dec(v___x_41_);
lean_dec(v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0(lean_object* v_00_u03b9_43_, lean_object* v_s_44_, lean_object* v_f_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v_s_44_, v_f_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_qbinom(lean_object* v_q_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_zero_50_; uint8_t v_isZero_51_; 
v_zero_50_ = lean_unsigned_to_nat(0u);
v_isZero_51_ = lean_nat_dec_eq(v_x_49_, v_zero_50_);
if (v_isZero_51_ == 1)
{
lean_object* v___x_52_; 
v___x_52_ = lean_unsigned_to_nat(1u);
return v___x_52_;
}
else
{
uint8_t v_isZero_53_; 
v_isZero_53_ = lean_nat_dec_eq(v_x_48_, v_zero_50_);
if (v_isZero_53_ == 1)
{
return v_zero_50_;
}
else
{
lean_object* v_one_54_; lean_object* v_n_55_; lean_object* v_n_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_one_54_ = lean_unsigned_to_nat(1u);
v_n_55_ = lean_nat_sub(v_x_49_, v_one_54_);
v_n_56_ = lean_nat_sub(v_x_48_, v_one_54_);
v___x_57_ = lp_tree_Formalism_HadamardInequality_qbinom(v_q_47_, v_n_56_, v_n_55_);
v___x_58_ = lean_nat_add(v_n_55_, v_one_54_);
lean_dec(v_n_55_);
v___x_59_ = lean_nat_pow(v_q_47_, v___x_58_);
v___x_60_ = lp_tree_Formalism_HadamardInequality_qbinom(v_q_47_, v_n_56_, v___x_58_);
lean_dec(v___x_58_);
lean_dec(v_n_56_);
v___x_61_ = lean_nat_mul(v___x_59_, v___x_60_);
lean_dec(v___x_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_nat_add(v___x_57_, v___x_61_);
lean_dec(v___x_61_);
lean_dec(v___x_57_);
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_qbinom___boxed(lean_object* v_q_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_HadamardInequality_qbinom(v_q_63_, v_x_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_x_64_);
lean_dec(v_q_63_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_zdual(lean_object* v_E_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_M_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HadamardInequality_zdual___boxed(lean_object* v_E_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_M_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_HadamardInequality_zdual(v_E_72_, v_inst_73_, v_inst_74_, v_M_75_);
lean_dec_ref(v_inst_74_);
lean_dec_ref(v_inst_73_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GelfandTransference_EnergyIdentity(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
