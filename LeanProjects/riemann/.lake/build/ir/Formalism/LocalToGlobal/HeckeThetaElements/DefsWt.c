// Lean compiler output
// Module: Formalism.LocalToGlobal.HeckeThetaElements.DefsWt
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_floor(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_NTheta_lamAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NTheta_lamAt___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_lamAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_lamAt___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Int_floor___at___00Formalism_L2_NTheta_kapW_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_NTheta_lamAt___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_lamAt(lean_object* v_R_3_, lean_object* v_h_4_, lean_object* v_n_5_){
_start:
{
lean_object* v_k_6_; lean_object* v_m_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_k_6_ = lean_ctor_get(v_R_3_, 1);
v_m_7_ = lean_ctor_get(v_R_3_, 2);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_sub(v_k_6_, v___x_8_);
v___x_10_ = lean_nat_dec_lt(v_n_5_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_nat_sub(v_n_5_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v_n_5_);
v___x_12_ = lean_nat_dec_lt(v___x_11_, v_m_7_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v___x_11_);
lean_dec_ref(v_h_4_);
v___x_13_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_lamAt___closed__0, &lp_tree_Formalism_L2_NTheta_lamAt___closed__0_once, _init_lp_tree_Formalism_L2_NTheta_lamAt___closed__0);
return v___x_13_;
}
else
{
lean_object* v_b_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_b_14_ = lean_ctor_get(v_h_4_, 2);
lean_inc_ref(v_b_14_);
lean_dec_ref(v_h_4_);
v___x_15_ = lean_apply_1(v_b_14_, v___x_11_);
v___x_16_ = l_Rat_neg(v___x_15_);
return v___x_16_;
}
}
else
{
lean_object* v_v_17_; lean_object* v___x_18_; 
lean_dec(v___x_9_);
v_v_17_ = lean_ctor_get(v_h_4_, 1);
lean_inc_ref(v_v_17_);
lean_dec_ref(v_h_4_);
v___x_18_ = lean_apply_1(v_v_17_, v_n_5_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_lamAt___boxed(lean_object* v_R_19_, lean_object* v_h_20_, lean_object* v_n_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_NTheta_lamAt(v_R_19_, v_h_20_, v_n_21_);
lean_dec_ref(v_R_19_);
return v_res_22_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__0(lean_object* v_p_27_, lean_object* v_R_28_, lean_object* v_h_29_, lean_object* v_q_30_, lean_object* v_c_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_32_ = lean_nat_add(v_p_27_, v_c_31_);
v___x_33_ = lp_tree_Formalism_L2_NTheta_lamAt(v_R_28_, v_h_29_, v___x_32_);
v___x_34_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_p_27_);
v___x_35_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0, &lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0);
v___x_36_ = l_Rat_div(v___x_34_, v___x_35_);
lean_dec_ref(v___x_34_);
v___x_37_ = l_Rat_sub(v___x_33_, v___x_36_);
v___x_38_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_q_30_);
v___x_39_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1, &lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1_once, _init_lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1);
v___x_40_ = l_Rat_sub(v___x_38_, v___x_39_);
v___x_41_ = l_Rat_div(v___x_40_, v___x_35_);
lean_dec_ref(v___x_40_);
v___x_42_ = l_Rat_sub(v___x_37_, v___x_41_);
v___x_43_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_c_31_);
v___x_44_ = l_Rat_add(v___x_42_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__0___boxed(lean_object* v_p_45_, lean_object* v_R_46_, lean_object* v_h_47_, lean_object* v_q_48_, lean_object* v_c_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_L2_NTheta_kapQ___lam__0(v_p_45_, v_R_46_, v_h_47_, v_q_48_, v_c_49_);
lean_dec_ref(v_R_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__1(lean_object* v_R_51_, lean_object* v_h_52_, lean_object* v_q_53_, lean_object* v_p_54_, lean_object* v_i_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
lean_inc(v_i_55_);
v___x_56_ = lp_tree_Formalism_L2_NTheta_lamAt(v_R_51_, v_h_52_, v_i_55_);
v___x_57_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_q_53_);
v___x_58_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0, &lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__0);
v___x_59_ = l_Rat_div(v___x_57_, v___x_58_);
lean_dec_ref(v___x_57_);
v___x_60_ = l_Rat_add(v___x_56_, v___x_59_);
v___x_61_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_p_54_);
v___x_62_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1, &lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1_once, _init_lp_tree_Formalism_L2_NTheta_kapQ___lam__0___closed__1);
v___x_63_ = l_Rat_sub(v___x_61_, v___x_62_);
v___x_64_ = l_Rat_div(v___x_63_, v___x_58_);
lean_dec_ref(v___x_63_);
v___x_65_ = l_Rat_sub(v___x_60_, v___x_64_);
v___x_66_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_55_);
v___x_67_ = l_Rat_add(v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ___lam__1___boxed(lean_object* v_R_68_, lean_object* v_h_69_, lean_object* v_q_70_, lean_object* v_p_71_, lean_object* v_i_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_tree_Formalism_L2_NTheta_kapQ___lam__1(v_R_68_, v_h_69_, v_q_70_, v_p_71_, v_i_72_);
lean_dec_ref(v_R_68_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapQ(lean_object* v_R_74_, lean_object* v_h_75_, lean_object* v_p_76_, lean_object* v_q_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; 
lean_inc(v_q_77_);
lean_inc_ref(v_h_75_);
lean_inc_ref(v_R_74_);
lean_inc(v_p_76_);
v___f_79_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NTheta_kapQ___lam__0___boxed), 5, 4);
lean_closure_set(v___f_79_, 0, v_p_76_);
lean_closure_set(v___f_79_, 1, v_R_74_);
lean_closure_set(v___f_79_, 2, v_h_75_);
lean_closure_set(v___f_79_, 3, v_q_77_);
v___f_80_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NTheta_kapQ___lam__1___boxed), 5, 4);
lean_closure_set(v___f_80_, 0, v_R_74_);
lean_closure_set(v___f_80_, 1, v_h_75_);
lean_closure_set(v___f_80_, 2, v_q_77_);
lean_closure_set(v___f_80_, 3, v_p_76_);
v___x_81_ = l_Sum_elim___redArg(v___f_80_, v___f_79_, v_a_78_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Int_floor___at___00Formalism_L2_NTheta_kapW_spec__0(lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Rat_floor(v_a_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_kapW(lean_object* v_R_84_, lean_object* v_h_85_, lean_object* v_p_86_, lean_object* v_q_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lp_tree_Formalism_L2_NTheta_kapQ(v_R_84_, v_h_85_, v_p_86_, v_q_87_, v_a_88_);
v___x_90_ = l_Rat_floor(v___x_89_);
return v___x_90_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HeckeThetaElements_IsHeckeElt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HeckeThetaElements_DefsWt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HeckeThetaElements_IsHeckeElt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
