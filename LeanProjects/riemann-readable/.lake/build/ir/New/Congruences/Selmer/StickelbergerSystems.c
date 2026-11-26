// Lean compiler output
// Module: New.Congruences.Selmer.StickelbergerSystems
// Imports: public import Init public meta import Init public import Lib.GaloisRep.Main.AttachedRepresentations public import Lib.General.NumberTheory.GaussValuation public import New.Congruences.Selmer.AuxiliaryPrimes
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
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0;
static lean_once_cell_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__1;
static lean_once_cell_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__2;
static lean_once_cell_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__3;
static lean_once_cell_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__4;
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Selmer_eulerFactor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Selmer_eulerFactor___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Selmer_eulerFactor___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_eulerFactor___redArg___lam__0(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_4_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_3_, v_a_1_, v_b_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__0___boxed(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lp_GRH_New_Selmer_eulerFactor___redArg___lam__0(v_a_5_, v_b_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__1(lean_object* v_toZPow_9_, lean_object* v_a_10_, lean_object* v_toNatCast_11_, lean_object* v_q_12_, lean_object* v_e_13_, lean_object* v_toMul_14_, lean_object* v_toSub_15_, lean_object* v_toOne_16_, lean_object* v_00_u03b5_17_){
_start:
{
lean_object* v_val_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_val_18_ = lean_ctor_get(v_00_u03b5_17_, 0);
lean_inc(v_val_18_);
lean_dec_ref(v_00_u03b5_17_);
lean_inc(v_toZPow_9_);
v___x_19_ = lean_apply_2(v_toZPow_9_, v_val_18_, v_a_10_);
v___x_20_ = lean_apply_1(v_toNatCast_11_, v_q_12_);
v___x_21_ = lean_int_neg(v_e_13_);
v___x_22_ = lean_apply_2(v_toZPow_9_, v___x_21_, v___x_20_);
v___x_23_ = lean_apply_2(v_toMul_14_, v___x_19_, v___x_22_);
v___x_24_ = lean_apply_2(v_toSub_15_, v_toOne_16_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__1___boxed(lean_object* v_toZPow_25_, lean_object* v_a_26_, lean_object* v_toNatCast_27_, lean_object* v_q_28_, lean_object* v_e_29_, lean_object* v_toMul_30_, lean_object* v_toSub_31_, lean_object* v_toOne_32_, lean_object* v_00_u03b5_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_Selmer_eulerFactor___redArg___lam__1(v_toZPow_25_, v_a_26_, v_toNatCast_27_, v_q_28_, v_e_29_, v_toMul_30_, v_toSub_31_, v_toOne_32_, v_00_u03b5_33_);
lean_dec(v_e_29_);
return v_res_34_;
}
}
static lean_object* _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0, &lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0_once, _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_obj_once(&lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0, &lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0_once, _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__0);
v___x_40_ = lean_int_neg(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__2, &lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__2_once, _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__2);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__4(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_box(0);
v___x_44_ = lean_obj_once(&lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__3, &lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__3_once, _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__3);
v___x_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2(lean_object* v_toZPow_46_, lean_object* v_a_47_, lean_object* v_toNatCast_48_, lean_object* v_q_49_, lean_object* v_toMul_50_, lean_object* v_toSub_51_, lean_object* v_toOne_52_, lean_object* v___f_53_, lean_object* v___x_54_, lean_object* v_e_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_56_ = lean_alloc_closure((void*)(lp_GRH_New_Selmer_eulerFactor___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_56_, 0, v_toZPow_46_);
lean_closure_set(v___f_56_, 1, v_a_47_);
lean_closure_set(v___f_56_, 2, v_toNatCast_48_);
lean_closure_set(v___f_56_, 3, v_q_49_);
lean_closure_set(v___f_56_, 4, v_e_55_);
lean_closure_set(v___f_56_, 5, v_toMul_50_);
lean_closure_set(v___f_56_, 6, v_toSub_51_);
lean_closure_set(v___f_56_, 7, v_toOne_52_);
v___x_57_ = lean_obj_once(&lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__1, &lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__1_once, _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__1);
v___x_58_ = lean_obj_once(&lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__4, &lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__4_once, _init_lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___closed__4);
v___x_59_ = lp_mathlib_Multiset_ndinsert___redArg(v___f_53_, v___x_57_, v___x_58_);
v___x_60_ = lp_mathlib_Finset_prod___redArg(v___x_54_, v___x_59_, v___f_56_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___boxed(lean_object* v_toZPow_61_, lean_object* v_a_62_, lean_object* v_toNatCast_63_, lean_object* v_q_64_, lean_object* v_toMul_65_, lean_object* v_toSub_66_, lean_object* v_toOne_67_, lean_object* v___f_68_, lean_object* v___x_69_, lean_object* v_e_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_GRH_New_Selmer_eulerFactor___redArg___lam__2(v_toZPow_61_, v_a_62_, v_toNatCast_63_, v_q_64_, v_toMul_65_, v_toSub_66_, v_toOne_67_, v___f_68_, v___x_69_, v_e_70_);
lean_dec_ref(v___x_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor___redArg(lean_object* v_inst_73_, lean_object* v_exps_74_, lean_object* v_a_75_, lean_object* v_q_76_){
_start:
{
lean_object* v___x_77_; lean_object* v_toCommSemiring_78_; lean_object* v___x_79_; lean_object* v_toMul_80_; lean_object* v___x_81_; lean_object* v_toRing_82_; lean_object* v___x_83_; lean_object* v_toAddMonoidWithOne_84_; lean_object* v_toNatCast_85_; lean_object* v_toOne_86_; lean_object* v_toCommRing_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_toSub_90_; lean_object* v___x_91_; lean_object* v_toZPow_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_77_ = lp_mathlib_Field_toSemifield___redArg(v_inst_73_);
v_toCommSemiring_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_toCommSemiring_78_);
lean_dec_ref(v___x_77_);
v___x_79_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_78_);
v_toMul_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_n(v_toMul_80_, 2);
lean_dec_ref(v___x_79_);
lean_inc_ref(v_inst_73_);
v___x_81_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_73_);
v_toRing_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_toRing_82_);
v___x_83_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_82_);
v_toAddMonoidWithOne_84_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_toAddMonoidWithOne_84_);
v_toNatCast_85_ = lean_ctor_get(v_toAddMonoidWithOne_84_, 0);
lean_inc(v_toNatCast_85_);
v_toOne_86_ = lean_ctor_get(v_toAddMonoidWithOne_84_, 2);
lean_inc_n(v_toOne_86_, 2);
lean_dec_ref(v_toAddMonoidWithOne_84_);
v_toCommRing_87_ = lean_ctor_get(v_inst_73_, 0);
lean_inc_ref(v_toCommRing_87_);
lean_dec_ref(v_inst_73_);
v___x_88_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_87_);
lean_dec_ref(v_toCommRing_87_);
v___x_89_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_83_);
lean_dec_ref(v___x_83_);
v_toSub_90_ = lean_ctor_get(v___x_89_, 2);
lean_inc(v_toSub_90_);
lean_dec_ref(v___x_89_);
v___x_91_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_81_);
lean_dec_ref(v___x_81_);
v_toZPow_92_ = lean_ctor_get(v___x_91_, 3);
lean_inc(v_toZPow_92_);
lean_dec_ref(v___x_91_);
v___f_93_ = ((lean_object*)(lp_GRH_New_Selmer_eulerFactor___redArg___closed__0));
v___f_94_ = lean_alloc_closure((void*)(lp_GRH_New_Selmer_eulerFactor___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_94_, 0, v_toZPow_92_);
lean_closure_set(v___f_94_, 1, v_a_75_);
lean_closure_set(v___f_94_, 2, v_toNatCast_85_);
lean_closure_set(v___f_94_, 3, v_q_76_);
lean_closure_set(v___f_94_, 4, v_toMul_80_);
lean_closure_set(v___f_94_, 5, v_toSub_90_);
lean_closure_set(v___f_94_, 6, v_toOne_86_);
lean_closure_set(v___f_94_, 7, v___f_93_);
lean_closure_set(v___f_94_, 8, v___x_88_);
v___x_95_ = lean_box(0);
v___x_96_ = l_List_mapTR_loop___redArg(v___f_94_, v_exps_74_, v___x_95_);
v___x_97_ = l_List_prod___redArg(v_toMul_80_, v_toOne_86_, v___x_96_);
lean_dec(v_toOne_86_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_eulerFactor(lean_object* v_K_98_, lean_object* v_inst_99_, lean_object* v_exps_100_, lean_object* v_a_101_, lean_object* v_q_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_GRH_New_Selmer_eulerFactor___redArg(v_inst_99_, v_exps_100_, v_a_101_, v_q_102_);
return v___x_103_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Main_AttachedRepresentations(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_GaussValuation(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Selmer_StickelbergerSystems(uint8_t builtin) {
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
res = initialize_GRH_Lib_GaloisRep_Main_AttachedRepresentations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_GaussValuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
