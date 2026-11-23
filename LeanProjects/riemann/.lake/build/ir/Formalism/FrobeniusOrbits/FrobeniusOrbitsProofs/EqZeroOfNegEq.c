// Lean compiler output
// Module: Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.HostThickExists public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
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
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_quadraticChar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* lp_mathlib_MulChar_ringHomComp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_AddChar_zmodChar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_gaussSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_gs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_gs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg(lean_object* v_p_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_toCommRing_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; 
lean_inc(v_p_1_);
v___x_3_ = lp_mathlib_ZMod_instField___redArg(v_p_1_);
v_toCommRing_4_ = lean_ctor_get(v_inst_2_, 0);
v___x_5_ = lp_mathlib_ZMod_fintype___redArg(v_p_1_);
v___x_6_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_6_, 0, v_p_1_);
v___x_7_ = lp_mathlib_quadraticChar___redArg(v___x_3_, v___x_5_, v___x_6_);
lean_dec_ref(v___x_3_);
v___x_8_ = lp_mathlib_Ring_toNonAssocRing___redArg(v_toCommRing_4_);
v___x_9_ = lp_mathlib_Int_castRingHom___redArg(v___x_8_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_MulChar_ringHomComp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_7_);
lean_closure_set(v___f_10_, 1, v___x_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg___boxed(lean_object* v_p_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg(v_p_11_, v_inst_12_);
lean_dec_ref(v_inst_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi(lean_object* v_p_14_, lean_object* v_inst_15_, lean_object* v_K_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg(v_p_14_, v_inst_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_chi___boxed(lean_object* v_p_19_, lean_object* v_inst_20_, lean_object* v_K_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_FrobeniusOrbits_Cond_chi(v_p_19_, v_inst_20_, v_K_21_, v_inst_22_);
lean_dec_ref(v_inst_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_gs___redArg(lean_object* v_inst_24_, lean_object* v_p_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_toCommRing_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_toCommRing_27_ = lean_ctor_get(v_inst_24_, 0);
lean_inc_ref(v_toCommRing_27_);
v___x_28_ = lp_mathlib_ZMod_fintype___redArg(v_p_25_);
lean_inc(v_p_25_);
v___x_29_ = lp_tree_Formalism_FrobeniusOrbits_Cond_chi___redArg(v_p_25_, v_inst_24_);
lean_dec_ref(v_inst_24_);
v___x_30_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_27_);
v___x_31_ = lp_mathlib_AddChar_zmodChar___redArg(v___x_30_, v_p_25_, v_x_26_);
v___x_32_ = lp_mathlib_gaussSum___redArg(v___x_28_, v_toCommRing_27_, v___x_29_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_Cond_gs(lean_object* v_K_33_, lean_object* v_inst_34_, lean_object* v_p_35_, lean_object* v_inst_36_, lean_object* v_x_37_, lean_object* v_hx_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree_Formalism_FrobeniusOrbits_Cond_gs___redArg(v_inst_34_, v_p_35_, v_x_37_);
return v___x_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostThickExists(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_HostThickExists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
