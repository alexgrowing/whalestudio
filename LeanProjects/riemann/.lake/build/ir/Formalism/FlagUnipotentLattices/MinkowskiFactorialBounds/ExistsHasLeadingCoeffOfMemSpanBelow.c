// Lean compiler output
// Module: Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
// Imports: public import Init public meta import Init public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_perpS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_perpS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_perpS(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_V_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_H_7_, lean_object* v_S_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_perpS___boxed(lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_V_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_H_16_, lean_object* v_S_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_HermitianLatticeCounting_P_perpS(v_K_10_, v_inst_11_, v_inst_12_, v_V_13_, v_inst_14_, v_inst_15_, v_H_16_, v_S_17_);
lean_dec(v_H_16_);
lean_dec(v_inst_15_);
lean_dec_ref(v_inst_14_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___lam__0(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_p_21_, lean_object* v_s_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
lean_inc_ref(v_inst_20_);
lean_inc(v_p_21_);
v___x_29_ = lean_apply_2(v_inst_20_, v_b_24_, v_p_21_);
v___x_30_ = lean_apply_2(v_inst_20_, v_a_23_, v_p_21_);
v___x_31_ = lean_unbox(v___x_30_);
if (v___x_31_ == 0)
{
goto v___jp_25_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = lean_unbox(v___x_29_);
if (v___x_32_ == 0)
{
goto v___jp_25_;
}
else
{
lean_dec_ref(v_inst_19_);
lean_inc(v_s_22_);
return v_s_22_;
}
}
v___jp_25_:
{
lean_object* v_toSemiring_26_; lean_object* v___x_27_; lean_object* v_toZero_28_; 
v_toSemiring_26_ = lean_ctor_get(v_inst_19_, 0);
lean_inc_ref(v_toSemiring_26_);
lean_dec_ref(v_inst_19_);
v___x_27_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_26_);
v_toZero_28_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_toZero_28_);
lean_dec_ref(v___x_27_);
return v_toZero_28_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___lam__0___boxed(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_p_35_, lean_object* v_s_36_, lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___lam__0(v_inst_33_, v_inst_34_, v_p_35_, v_s_36_, v_a_37_, v_b_38_);
lean_dec(v_s_36_);
return v_res_39_;
}
}
static lean_object* _init_lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_p_43_, lean_object* v_s_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; lean_object* v_toFun_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___closed__0, &lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___closed__0_once, _init_lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___closed__0);
v_toFun_48_ = lean_ctor_get(v___x_47_, 0);
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_49_, 0, v_inst_41_);
lean_closure_set(v___f_49_, 1, v_inst_42_);
lean_closure_set(v___f_49_, 2, v_p_43_);
lean_closure_set(v___f_49_, 3, v_s_44_);
lean_inc(v_toFun_48_);
v___x_50_ = lean_apply_3(v_toFun_48_, v___f_49_, v_a_45_, v_a_46_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_P_Esing(lean_object* v_R_51_, lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_inst_54_, lean_object* v_p_55_, lean_object* v_s_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_HermitianLatticeCounting_P_Esing___redArg(v_inst_52_, v_inst_54_, v_p_55_, v_s_56_, v_a_57_, v_a_58_);
return v___x_59_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
