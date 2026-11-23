// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
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
lean_object* lp_mathlib_ZMod_finEquiv___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_addCommGroup___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquiv___redArg(lean_object* v_inst_1_, lean_object* v_e_2_, lean_object* v_n_3_, lean_object* v_00_u03b5_4_, lean_object* v_h_x27_5_, lean_object* v_a_x27_6_){
_start:
{
lean_object* v___x_7_; lean_object* v_toFun_8_; lean_object* v___x_9_; lean_object* v_toFun_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc_ref(v_00_u03b5_4_);
v___x_7_ = lp_mathlib_Equiv_addCommGroup___redArg(v_00_u03b5_4_, v_inst_1_);
v_toFun_8_ = lean_ctor_get(v_00_u03b5_4_, 0);
lean_inc(v_toFun_8_);
v___x_9_ = lp_mathlib_Equiv_symm___redArg(v_00_u03b5_4_);
v_toFun_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_toFun_10_);
lean_dec_ref(v___x_9_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_toFun_8_);
lean_closure_set(v___f_11_, 1, v_h_x27_5_);
v___x_12_ = lean_apply_1(v_toFun_10_, v_a_x27_6_);
v___x_13_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_13_, 0, v_e_2_);
lean_ctor_set(v___x_13_, 1, v_n_3_);
lean_ctor_set(v___x_13_, 2, v___x_7_);
lean_ctor_set(v___x_13_, 3, v___f_11_);
lean_ctor_set(v___x_13_, 4, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquiv(lean_object* v_A_x27_14_, lean_object* v_inst_15_, lean_object* v_e_16_, lean_object* v_n_17_, lean_object* v_00_u03b5_18_, lean_object* v_h_x27_19_, lean_object* v_hs_20_, lean_object* v_a_x27_21_, lean_object* v_hk_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Formalism_HC_Frame_ofEquiv___redArg(v_inst_15_, v_e_16_, v_n_17_, v_00_u03b5_18_, v_h_x27_19_, v_a_x27_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso___redArg(lean_object* v_00_u03b5_24_){
_start:
{
lean_inc_ref(v_00_u03b5_24_);
return v_00_u03b5_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso___redArg___boxed(lean_object* v_00_u03b5_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_HC_Frame_ofEquivIso___redArg(v_00_u03b5_25_);
lean_dec_ref(v_00_u03b5_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso(lean_object* v_A_x27_27_, lean_object* v_inst_28_, lean_object* v_e_29_, lean_object* v_n_30_, lean_object* v_00_u03b5_31_, lean_object* v_h_x27_32_, lean_object* v_hs_33_, lean_object* v_a_x27_34_, lean_object* v_hk_35_){
_start:
{
lean_inc_ref(v_00_u03b5_31_);
return v_00_u03b5_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofEquivIso___boxed(lean_object* v_A_x27_36_, lean_object* v_inst_37_, lean_object* v_e_38_, lean_object* v_n_39_, lean_object* v_00_u03b5_40_, lean_object* v_h_x27_41_, lean_object* v_hs_42_, lean_object* v_a_x27_43_, lean_object* v_hk_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_HC_Frame_ofEquivIso(v_A_x27_36_, v_inst_37_, v_e_38_, v_n_39_, v_00_u03b5_40_, v_h_x27_41_, v_hs_42_, v_a_x27_43_, v_hk_44_);
lean_dec(v_a_x27_43_);
lean_dec(v_h_x27_41_);
lean_dec_ref(v_00_u03b5_40_);
lean_dec(v_n_39_);
lean_dec(v_e_38_);
lean_dec_ref(v_inst_37_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod___redArg(lean_object* v_n_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_mathlib_ZMod_finEquiv___redArg(v_n_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod___redArg___boxed(lean_object* v_n_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_HC_idxZMod___redArg(v_n_48_);
lean_dec(v_n_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod(lean_object* v_n_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_mathlib_ZMod_finEquiv___redArg(v_n_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_idxZMod___boxed(lean_object* v_n_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_HC_idxZMod(v_n_53_, v_inst_54_);
lean_dec(v_n_53_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
