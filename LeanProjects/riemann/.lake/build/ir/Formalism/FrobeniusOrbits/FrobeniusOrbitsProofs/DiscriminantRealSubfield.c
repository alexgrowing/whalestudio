// Lean compiler output
// Module: Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_Fz(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_Fz___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__1___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__0 = (const lean_object*)&lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__0_value;
static const lean_closure_object lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__1 = (const lean_object*)&lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__1_value;
static const lean_ctor_object lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__0_value),((lean_object*)&lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__1_value)}};
static const lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__2 = (const lean_object*)&lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__2_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th___redArg(lean_object* v_inst_1_, lean_object* v_z_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v_toSemiring_5_; lean_object* v___x_6_; lean_object* v_toAdd_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toInv_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_3_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
lean_inc_ref(v___x_3_);
v___x_4_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_3_);
v_toSemiring_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_5_);
v_toAdd_7_ = lean_ctor_get(v___x_6_, 1);
lean_inc(v_toAdd_7_);
lean_dec_ref(v___x_6_);
v___x_8_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_3_);
lean_dec_ref(v___x_3_);
v___x_9_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_8_);
v___x_10_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_9_);
lean_dec_ref(v___x_9_);
v_toInv_11_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_toInv_11_);
lean_dec_ref(v___x_10_);
lean_inc(v_z_2_);
v___x_12_ = lean_apply_1(v_toInv_11_, v_z_2_);
v___x_13_ = lean_apply_2(v_toAdd_7_, v_z_2_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th___redArg___boxed(lean_object* v_inst_14_, lean_object* v_z_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_FrobeniusOrbits_Discr_th___redArg(v_inst_14_, v_z_15_);
lean_dec_ref(v_inst_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th(lean_object* v_K_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_z_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_tree_Formalism_FrobeniusOrbits_Discr_th___redArg(v_inst_18_, v_z_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_th___boxed(lean_object* v_K_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_z_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_FrobeniusOrbits_Discr_th(v_K_22_, v_inst_23_, v_inst_24_, v_z_25_);
lean_dec_ref(v_inst_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_Fz(lean_object* v_L_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_00_u03b6_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_Fz___boxed(lean_object* v_L_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_00_u03b6_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_FrobeniusOrbits_Discr_Fz(v_L_32_, v_inst_33_, v_inst_34_, v_00_u03b6_35_);
lean_dec(v_00_u03b6_35_);
lean_dec_ref(v_inst_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__0(lean_object* v_x_37_){
_start:
{
lean_inc(v_x_37_);
return v_x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__0___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__0(v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__1(lean_object* v_y_40_){
_start:
{
lean_inc(v_y_40_);
return v_y_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__1___boxed(lean_object* v_y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___lam__1(v_y_41_);
lean_dec(v_y_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF(lean_object* v_L_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_00_u03b6_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___closed__2));
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Discr_equivF___boxed(lean_object* v_L_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_00_u03b6_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_Formalism_FrobeniusOrbits_Discr_equivF(v_L_53_, v_inst_54_, v_inst_55_, v_00_u03b6_56_);
lean_dec(v_00_u03b6_56_);
lean_dec_ref(v_inst_54_);
return v_res_57_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
