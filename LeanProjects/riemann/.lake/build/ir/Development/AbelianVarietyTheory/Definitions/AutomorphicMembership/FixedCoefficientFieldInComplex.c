// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.RootValueClassBasis
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_tree_Subsemiring_subtype___at___00GlobalTheory_Mem_Base_OtoLL_spec__4___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Fld_natIdeal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Fld_natIdeal___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_GlobalTheory_Mem_Fld_modulus___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_GlobalTheory_Mem_Fld_modulus___closed__0;
static lean_once_cell_t lp_tree_GlobalTheory_Mem_Fld_modulus___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_GlobalTheory_Mem_Fld_modulus___closed__1;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Fld_modulus(lean_object*);
static const lean_closure_object lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subsemiring_subtype___at___00GlobalTheory_Mem_Base_OtoLL_spec__4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex___closed__0 = (const lean_object*)&lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Base_KstoC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Fld_natIdeal(lean_object* v_E_1_, lean_object* v_inst_2_, lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Fld_natIdeal___boxed(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_GlobalTheory_Mem_Fld_natIdeal(v_E_5_, v_inst_6_, v_n_7_);
lean_dec(v_n_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
static lean_object* _init_lp_tree_GlobalTheory_Mem_Fld_modulus___closed__0(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_unsigned_to_nat(2u);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_nat_mod(v___x_10_, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_lp_tree_GlobalTheory_Mem_Fld_modulus___closed__1(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_mod(v___x_13_, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Fld_modulus(lean_object* v_P_15_){
_start:
{
lean_object* v_host_16_; lean_object* v_g_17_; lean_object* v_pde_18_; lean_object* v_pde_x27_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_host_16_ = lean_ctor_get(v_P_15_, 1);
lean_inc_ref(v_host_16_);
lean_dec_ref(v_P_15_);
v_g_17_ = lean_ctor_get(v_host_16_, 6);
lean_inc_ref_n(v_g_17_, 2);
v_pde_18_ = lean_ctor_get(v_host_16_, 7);
lean_inc(v_pde_18_);
v_pde_x27_19_ = lean_ctor_get(v_host_16_, 8);
lean_inc(v_pde_x27_19_);
lean_dec_ref(v_host_16_);
v___x_20_ = lean_obj_once(&lp_tree_GlobalTheory_Mem_Fld_modulus___closed__0, &lp_tree_GlobalTheory_Mem_Fld_modulus___closed__0_once, _init_lp_tree_GlobalTheory_Mem_Fld_modulus___closed__0);
v___x_21_ = lean_apply_1(v_g_17_, v___x_20_);
v___x_22_ = lean_obj_once(&lp_tree_GlobalTheory_Mem_Fld_modulus___closed__1, &lp_tree_GlobalTheory_Mem_Fld_modulus___closed__1_once, _init_lp_tree_GlobalTheory_Mem_Fld_modulus___closed__1);
v___x_23_ = lean_apply_1(v_g_17_, v___x_22_);
v___x_24_ = lean_nat_mul(v___x_21_, v___x_23_);
lean_dec(v___x_23_);
lean_dec(v___x_21_);
v___x_25_ = lean_nat_mul(v___x_24_, v_pde_18_);
lean_dec(v_pde_18_);
lean_dec(v___x_24_);
v___x_26_ = lean_nat_mul(v___x_25_, v_pde_x27_19_);
lean_dec(v_pde_x27_19_);
lean_dec(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex(lean_object* v_B_28_){
_start:
{
lean_object* v_embLL_29_; lean_object* v___f_30_; lean_object* v___f_31_; 
v_embLL_29_ = lean_ctor_get(v_B_28_, 3);
lean_inc_ref(v_embLL_29_);
lean_dec_ref(v_B_28_);
v___f_30_ = ((lean_object*)(lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex___closed__0));
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_31_, 0, v___f_30_);
lean_closure_set(v___f_31_, 1, v_embLL_29_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Base_KstoC(lean_object* v_B_32_){
_start:
{
lean_object* v_embLL_33_; lean_object* v___f_34_; lean_object* v___f_35_; 
v_embLL_33_ = lean_ctor_get(v_B_32_, 3);
lean_inc_ref(v_embLL_33_);
lean_dec_ref(v_B_32_);
v___f_34_ = ((lean_object*)(lp_tree_GlobalTheory_Mem_Base_AutomorphicRingToComplex___closed__0));
v___f_35_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_35_, 0, v___f_34_);
lean_closure_set(v___f_35_, 1, v_embLL_33_);
return v___f_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_Foundations_RootOfUnityEightQMemCoeffGaloisSubfield(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsRationalUnitaryDeterminantMapRationalUnitaryTo(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LFunctionPositiveConductorFourEight(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_PublishedTheorems_Divisors_u2082_CmCurveGoodOutsidePrimePremises(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_BlockTheory_JetGauges_RootValueClassBasis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_FixedCoefficientFieldInComplex(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_Foundations_RootOfUnityEightQMemCoeffGaloisSubfield(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsRationalUnitaryDeterminantMapRationalUnitaryTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LFunctionPositiveConductorFourEight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_PublishedTheorems_Divisors_u2082_CmCurveGoodOutsidePrimePremises(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_BlockTheory_JetGauges_RootValueClassBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
