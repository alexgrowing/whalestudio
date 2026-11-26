// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.Depth
// Imports: public import Init public meta import Init public import Lib.General.Algebra.MultivariatePolynomials public import New.UpperBound.ElementaryDivisors.TwistingData
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder___redArg(lean_object* v_T_1_, lean_object* v_r_2_, lean_object* v_v_3_){
_start:
{
lean_object* v_p_4_; lean_object* v_frobExp_5_; lean_object* v_fst_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___y_10_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_p_4_ = lean_ctor_get(v_T_1_, 0);
v_frobExp_5_ = lean_ctor_get(v_T_1_, 1);
v_fst_6_ = lean_ctor_get(v_v_3_, 0);
lean_inc(v_fst_6_);
v___x_7_ = lean_nat_pow(v_p_4_, v_frobExp_5_);
v___x_8_ = lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(v_T_1_, v_r_2_, v_v_3_);
v___x_13_ = lean_unsigned_to_nat(2u);
v___x_14_ = lean_nat_mul(v___x_13_, v_r_2_);
v___x_15_ = lean_nat_dec_le(v___x_14_, v_fst_6_);
lean_dec(v_fst_6_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_dec(v___x_14_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___y_10_ = v___x_16_;
goto v___jp_9_;
}
else
{
v___y_10_ = v___x_14_;
goto v___jp_9_;
}
v___jp_9_:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_nat_mul(v___x_8_, v___y_10_);
lean_dec(v___y_10_);
lean_dec(v___x_8_);
v___x_12_ = lean_nat_pow(v___x_7_, v___x_11_);
lean_dec(v___x_11_);
lean_dec(v___x_7_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder___redArg___boxed(lean_object* v_T_17_, lean_object* v_r_18_, lean_object* v_v_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_FrobeniusCycle_deepOrder___redArg(v_T_17_, v_r_18_, v_v_19_);
lean_dec(v_r_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder(lean_object* v_N_21_, lean_object* v_k_22_, lean_object* v_W_23_, lean_object* v_K_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_T_28_, lean_object* v_r_29_, lean_object* v_v_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_GRH_New_FrobeniusCycle_deepOrder___redArg(v_T_28_, v_r_29_, v_v_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepOrder___boxed(lean_object* v_N_32_, lean_object* v_k_33_, lean_object* v_W_34_, lean_object* v_K_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_T_39_, lean_object* v_r_40_, lean_object* v_v_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_GRH_New_FrobeniusCycle_deepOrder(v_N_32_, v_k_33_, v_W_34_, v_K_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_T_39_, v_r_40_, v_v_41_);
lean_dec(v_r_40_);
lean_dec_ref(v_inst_38_);
lean_dec_ref(v_inst_36_);
lean_dec(v_k_33_);
lean_dec(v_N_32_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow___redArg(lean_object* v_t_43_){
_start:
{
lean_object* v_fst_44_; 
v_fst_44_ = lean_ctor_get(v_t_43_, 0);
lean_inc(v_fst_44_);
return v_fst_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow___redArg___boxed(lean_object* v_t_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_GRH_New_FrobeniusCycle_entryRow___redArg(v_t_45_);
lean_dec_ref(v_t_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow(lean_object* v_k_47_, lean_object* v_r_48_, lean_object* v_m_49_, lean_object* v_hm_50_, lean_object* v_t_51_){
_start:
{
lean_object* v_fst_52_; 
v_fst_52_ = lean_ctor_get(v_t_51_, 0);
lean_inc(v_fst_52_);
return v_fst_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryRow___boxed(lean_object* v_k_53_, lean_object* v_r_54_, lean_object* v_m_55_, lean_object* v_hm_56_, lean_object* v_t_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_GRH_New_FrobeniusCycle_entryRow(v_k_53_, v_r_54_, v_m_55_, v_hm_56_, v_t_57_);
lean_dec_ref(v_t_57_);
lean_dec(v_m_55_);
lean_dec(v_r_54_);
lean_dec(v_k_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol___redArg(lean_object* v_k_59_, lean_object* v_r_60_, lean_object* v_m_61_, lean_object* v_t_62_){
_start:
{
lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_fst_63_ = lean_ctor_get(v_t_62_, 0);
v_snd_64_ = lean_ctor_get(v_t_62_, 1);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v_m_61_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_mod(v___x_67_, v___x_66_);
lean_dec(v___x_66_);
v___x_69_ = lean_nat_dec_eq(v_snd_64_, v___x_68_);
lean_dec(v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_nat_sub(v_k_59_, v_snd_64_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; 
v___x_71_ = lean_nat_add(v_fst_63_, v_r_60_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol___redArg___boxed(lean_object* v_k_72_, lean_object* v_r_73_, lean_object* v_m_74_, lean_object* v_t_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_FrobeniusCycle_entryCol___redArg(v_k_72_, v_r_73_, v_m_74_, v_t_75_);
lean_dec_ref(v_t_75_);
lean_dec(v_m_74_);
lean_dec(v_r_73_);
lean_dec(v_k_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol(lean_object* v_k_77_, lean_object* v_r_78_, lean_object* v_m_79_, lean_object* v_hm_80_, lean_object* v_t_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lp_GRH_New_FrobeniusCycle_entryCol___redArg(v_k_77_, v_r_78_, v_m_79_, v_t_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_entryCol___boxed(lean_object* v_k_83_, lean_object* v_r_84_, lean_object* v_m_85_, lean_object* v_hm_86_, lean_object* v_t_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_GRH_New_FrobeniusCycle_entryCol(v_k_83_, v_r_84_, v_m_85_, v_hm_86_, v_t_87_);
lean_dec_ref(v_t_87_);
lean_dec(v_m_85_);
lean_dec(v_r_84_);
lean_dec(v_k_83_);
return v_res_88_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_TwistingData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_Depth(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_TwistingData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
