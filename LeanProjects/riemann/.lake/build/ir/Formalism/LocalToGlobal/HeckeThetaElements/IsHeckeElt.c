// Lean compiler output
// Module: Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
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
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holEnt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holEnt___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holEnt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_NTheta_holPar___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_NTheta_holPar___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_NTheta_holPar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_NTheta_holPar___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NTheta_holPar___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_NTheta_holPar___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_NTheta_holPar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_NTheta_holPar___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NTheta_holPar___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_NTheta_holPar___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_LevWt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_LevWt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holEnt___lam__0(lean_object* v_lam_5_, lean_object* v_p_6_, lean_object* v_q_7_, lean_object* v_i_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_inc(v_i_8_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_i_8_);
v___x_10_ = lean_apply_1(v_lam_5_, v___x_9_);
v___x_11_ = l_Rat_ofInt(v___x_10_);
v___x_12_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_p_6_);
v___x_13_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0, &lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0);
v___x_14_ = l_Rat_div(v___x_12_, v___x_13_);
lean_dec_ref(v___x_12_);
v___x_15_ = l_Rat_add(v___x_11_, v___x_14_);
v___x_16_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_q_7_);
v___x_17_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1, &lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1_once, _init_lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1);
v___x_18_ = l_Rat_sub(v___x_16_, v___x_17_);
v___x_19_ = l_Rat_div(v___x_18_, v___x_13_);
lean_dec_ref(v___x_18_);
v___x_20_ = l_Rat_add(v___x_15_, v___x_19_);
v___x_21_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_8_);
v___x_22_ = l_Rat_sub(v___x_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holEnt___lam__1(lean_object* v_lam_23_, lean_object* v_q_24_, lean_object* v_p_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc(v_i_26_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v_i_26_);
v___x_28_ = lean_apply_1(v_lam_23_, v___x_27_);
v___x_29_ = l_Rat_ofInt(v___x_28_);
v___x_30_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_q_24_);
v___x_31_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0, &lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__0);
v___x_32_ = l_Rat_div(v___x_30_, v___x_31_);
lean_dec_ref(v___x_30_);
v___x_33_ = l_Rat_sub(v___x_29_, v___x_32_);
v___x_34_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_p_25_);
v___x_35_ = lean_obj_once(&lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1, &lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1_once, _init_lp_tree_Formalism_L2_NTheta_holEnt___lam__0___closed__1);
v___x_36_ = l_Rat_sub(v___x_34_, v___x_35_);
v___x_37_ = l_Rat_div(v___x_36_, v___x_31_);
lean_dec_ref(v___x_36_);
v___x_38_ = l_Rat_add(v___x_33_, v___x_37_);
v___x_39_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_26_);
v___x_40_ = l_Rat_sub(v___x_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holEnt(lean_object* v_p_41_, lean_object* v_q_42_, lean_object* v_lam_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___x_47_; 
lean_inc(v_q_42_);
lean_inc(v_p_41_);
lean_inc_ref(v_lam_43_);
v___f_45_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NTheta_holEnt___lam__0), 4, 3);
lean_closure_set(v___f_45_, 0, v_lam_43_);
lean_closure_set(v___f_45_, 1, v_p_41_);
lean_closure_set(v___f_45_, 2, v_q_42_);
v___f_46_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NTheta_holEnt___lam__1), 4, 3);
lean_closure_set(v___f_46_, 0, v_lam_43_);
lean_closure_set(v___f_46_, 1, v_q_42_);
lean_closure_set(v___f_46_, 2, v_p_41_);
v___x_47_ = l_Sum_elim___redArg(v___f_46_, v___f_45_, v_a_44_);
return v___x_47_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_NTheta_holPar___lam__0(lean_object* v_x_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = 1;
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar___lam__0___boxed(lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = lp_tree_Formalism_L2_NTheta_holPar___lam__0(v_x_50_);
lean_dec(v_x_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_NTheta_holPar___lam__1(lean_object* v_x_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar___lam__1___boxed(lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = lp_tree_Formalism_L2_NTheta_holPar___lam__1(v_x_55_);
lean_dec(v_x_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar___lam__2(lean_object* v_p_58_, lean_object* v_q_59_, lean_object* v_lam_60_, lean_object* v___f_61_, lean_object* v___f_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
lean_inc_ref(v_a_63_);
v___x_64_ = lp_tree_Formalism_L2_NTheta_holEnt(v_p_58_, v_q_59_, v_lam_60_, v_a_63_);
v___x_65_ = l_Sum_elim___redArg(v___f_61_, v___f_62_, v_a_63_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_holPar(lean_object* v_p_69_, lean_object* v_q_70_, lean_object* v_lam_71_){
_start:
{
lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___f_72_ = ((lean_object*)(lp_tree_Formalism_L2_NTheta_holPar___closed__0));
v___f_73_ = ((lean_object*)(lp_tree_Formalism_L2_NTheta_holPar___closed__1));
lean_inc(v_q_70_);
lean_inc(v_p_69_);
v___f_74_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NTheta_holPar___lam__2), 6, 5);
lean_closure_set(v___f_74_, 0, v_p_69_);
lean_closure_set(v___f_74_, 1, v_q_70_);
lean_closure_set(v___f_74_, 2, v_lam_71_);
lean_closure_set(v___f_74_, 3, v___f_72_);
lean_closure_set(v___f_74_, 4, v___f_73_);
v___x_75_ = l_List_finRange(v_p_69_);
v___x_76_ = l_List_finRange(v_q_70_);
v___x_77_ = lp_mathlib_Multiset_disjSum___redArg(v___x_75_, v___x_76_);
v___x_78_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_74_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_LevWt(lean_object* v_D_79_, lean_object* v_X_80_, lean_object* v_Ap_81_, lean_object* v_A_82_, lean_object* v_V_83_, lean_object* v_N_84_, lean_object* v_lam_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NTheta_LevWt___boxed(lean_object* v_D_87_, lean_object* v_X_88_, lean_object* v_Ap_89_, lean_object* v_A_90_, lean_object* v_V_91_, lean_object* v_N_92_, lean_object* v_lam_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_tree_Formalism_L2_NTheta_LevWt(v_D_87_, v_X_88_, v_Ap_89_, v_A_90_, v_V_91_, v_N_92_, v_lam_93_);
lean_dec_ref(v_lam_93_);
lean_dec(v_N_92_);
lean_dec_ref(v_V_91_);
lean_dec_ref(v_A_90_);
lean_dec_ref(v_Ap_89_);
lean_dec_ref(v_X_88_);
lean_dec_ref(v_D_87_);
return v_res_94_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_AllTied(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_InnerProductFormulaField(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HeckeThetaElements_IsHeckeElt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_AllTied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_InnerProductFormulaField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
