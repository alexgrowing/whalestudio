// Lean compiler output
// Module: New.Congruences.Selmer.AuxiliaryPrimes
// Imports: public import Init public meta import Init public import Lib.ClassField.Global.CMSplittingCharacters public import Lib.ClassField.Global.Chebotarev public import Lib.ClassField.Global.ExistenceTheorem public import Lib.General.NumberTheory.FrobeniusOrbits
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd___redArg();
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_mk___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_mapMatrix___redArg(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Selmer_pointChar___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Selmer_reduceModPow___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Ideal_Quotient_mk___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Selmer_reduceModPow___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Selmer_reduceModPow___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Selmer_reduceModPow___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Selmer_reduceModPow___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Selmer_reduceModPow___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_Selmer_reduceModPow___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_RingHom_comp___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_GRH_New_Selmer_reduceModPow___redArg___closed__1_value),((lean_object*)&lp_GRH_New_Selmer_reduceModPow___redArg___closed__0_value)} };
static const lean_object* lp_GRH_New_Selmer_reduceModPow___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Selmer_reduceModPow___redArg___closed__2_value;
static lean_once_cell_t lp_GRH_New_Selmer_reduceModPow___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Selmer_reduceModPow___redArg___closed__3;
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reduceModPow___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reduceModPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reduceModPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Selmer_pointChar___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Multiplicative_toAdd___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__0(lean_object* v_y_2_, lean_object* v_h_3_, lean_object* v_g_4_, lean_object* v_q_5_, lean_object* v_toNPow_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___x_8_; lean_object* v_toFun_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_8_ = lean_obj_once(&lp_GRH_New_Selmer_pointChar___redArg___lam__0___closed__0, &lp_GRH_New_Selmer_pointChar___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Selmer_pointChar___redArg___lam__0___closed__0);
v_toFun_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_j_7_);
v___x_10_ = lean_apply_1(v_y_2_, v_j_7_);
v___x_11_ = lean_apply_2(v_h_3_, v_j_7_, v_g_4_);
lean_inc(v_toFun_9_);
v___x_12_ = lean_apply_1(v_toFun_9_, v___x_11_);
v___x_13_ = lp_mathlib_ZMod_val(v_q_5_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_apply_2(v_toNPow_6_, v___x_13_, v___x_10_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__0___boxed(lean_object* v_y_15_, lean_object* v_h_16_, lean_object* v_g_17_, lean_object* v_q_18_, lean_object* v_toNPow_19_, lean_object* v_j_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_GRH_New_Selmer_pointChar___redArg___lam__0(v_y_15_, v_h_16_, v_g_17_, v_q_18_, v_toNPow_19_, v_j_20_);
lean_dec(v_q_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__1(lean_object* v_y_22_, lean_object* v_h_23_, lean_object* v_q_24_, lean_object* v_toNPow_25_, lean_object* v___x_26_, lean_object* v_inst_27_, lean_object* v_g_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(lp_GRH_New_Selmer_pointChar___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_29_, 0, v_y_22_);
lean_closure_set(v___f_29_, 1, v_h_23_);
lean_closure_set(v___f_29_, 2, v_g_28_);
lean_closure_set(v___f_29_, 3, v_q_24_);
lean_closure_set(v___f_29_, 4, v_toNPow_25_);
v___x_30_ = lp_mathlib_Finset_prod___redArg(v___x_26_, v_inst_27_, v___f_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg___lam__1___boxed(lean_object* v_y_31_, lean_object* v_h_32_, lean_object* v_q_33_, lean_object* v_toNPow_34_, lean_object* v___x_35_, lean_object* v_inst_36_, lean_object* v_g_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_Selmer_pointChar___redArg___lam__1(v_y_31_, v_h_32_, v_q_33_, v_toNPow_34_, v___x_35_, v_inst_36_, v_g_37_);
lean_dec_ref(v___x_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_q_41_, lean_object* v_h_42_, lean_object* v_y_43_){
_start:
{
lean_object* v_toSemiring_44_; lean_object* v___x_45_; lean_object* v_toMonoid_46_; lean_object* v_toNPow_47_; lean_object* v___f_48_; 
v_toSemiring_44_ = lean_ctor_get(v_inst_39_, 0);
lean_inc_ref(v_toSemiring_44_);
v___x_45_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_39_);
lean_dec_ref(v_inst_39_);
v_toMonoid_46_ = lean_ctor_get(v_toSemiring_44_, 1);
lean_inc_ref(v_toMonoid_46_);
lean_dec_ref(v_toSemiring_44_);
v_toNPow_47_ = lean_ctor_get(v_toMonoid_46_, 2);
lean_inc(v_toNPow_47_);
lean_dec_ref(v_toMonoid_46_);
v___f_48_ = lean_alloc_closure((void*)(lp_GRH_New_Selmer_pointChar___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_48_, 0, v_y_43_);
lean_closure_set(v___f_48_, 1, v_h_42_);
lean_closure_set(v___f_48_, 2, v_q_41_);
lean_closure_set(v___f_48_, 3, v_toNPow_47_);
lean_closure_set(v___f_48_, 4, v___x_45_);
lean_closure_set(v___f_48_, 5, v_inst_40_);
return v___f_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar(lean_object* v_G_49_, lean_object* v_O_50_, lean_object* v_00_u03c3_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_q_55_, lean_object* v_inst_56_, lean_object* v_h_57_, lean_object* v_y_58_, lean_object* v_hy_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_GRH_New_Selmer_pointChar___redArg(v_inst_52_, v_inst_53_, v_q_55_, v_h_57_, v_y_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_pointChar___boxed(lean_object* v_G_61_, lean_object* v_O_62_, lean_object* v_00_u03c3_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_q_67_, lean_object* v_inst_68_, lean_object* v_h_69_, lean_object* v_y_70_, lean_object* v_hy_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_GRH_New_Selmer_pointChar(v_G_61_, v_O_62_, v_00_u03c3_63_, v_inst_64_, v_inst_65_, v_inst_66_, v_q_67_, v_inst_68_, v_h_69_, v_y_70_, v_hy_71_);
lean_dec_ref(v_inst_66_);
return v_res_72_;
}
}
static lean_object* _init_lp_GRH_New_Selmer_reduceModPow___redArg___closed__3(void){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; 
v___f_78_ = ((lean_object*)(lp_GRH_New_Selmer_reduceModPow___redArg___closed__2));
v___x_79_ = lp_mathlib_RingHom_mapMatrix___redArg(v___f_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reduceModPow___redArg(lean_object* v_00_u03c1_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___f_82_; 
v___x_81_ = lean_obj_once(&lp_GRH_New_Selmer_reduceModPow___redArg___closed__3, &lp_GRH_New_Selmer_reduceModPow___redArg___closed__3_once, _init_lp_GRH_New_Selmer_reduceModPow___redArg___closed__3);
v___f_82_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_82_, 0, v_00_u03c1_80_);
lean_closure_set(v___f_82_, 1, v___x_81_);
return v___f_82_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reduceModPow(lean_object* v_G_83_, lean_object* v_O_84_, lean_object* v_n_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_l_90_, lean_object* v_M_91_, lean_object* v_00_u03c1_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_GRH_New_Selmer_reduceModPow___redArg(v_00_u03c1_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reduceModPow___boxed(lean_object* v_G_94_, lean_object* v_O_95_, lean_object* v_n_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_l_101_, lean_object* v_M_102_, lean_object* v_00_u03c1_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_GRH_New_Selmer_reduceModPow(v_G_94_, v_O_95_, v_n_96_, v_inst_97_, v_inst_98_, v_inst_99_, v_inst_100_, v_l_101_, v_M_102_, v_00_u03c1_103_);
lean_dec(v_M_102_);
lean_dec(v_l_101_);
lean_dec_ref(v_inst_100_);
lean_dec_ref(v_inst_99_);
lean_dec(v_inst_98_);
lean_dec_ref(v_inst_97_);
return v_res_104_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Global_CMSplittingCharacters(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Global_Chebotarev(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Global_ExistenceTheorem(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_FrobeniusOrbits(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Global_CMSplittingCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Global_Chebotarev(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Global_ExistenceTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_FrobeniusOrbits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
