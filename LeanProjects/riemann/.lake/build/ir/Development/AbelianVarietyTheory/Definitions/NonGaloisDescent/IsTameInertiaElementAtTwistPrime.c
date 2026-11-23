// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
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
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_Matrix_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_matAct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0(lean_object* v_d_2_, lean_object* v_g_3_, lean_object* v_q_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toFun_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0___closed__0, &lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0___closed__0_once, _init_lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0___closed__0);
v_toFun_6_ = lean_ctor_get(v___x_5_, 0);
v___x_7_ = lean_apply_2(v_d_2_, v_q_4_, v_g_3_);
lean_inc(v_toFun_6_);
v___x_8_ = lean_apply_1(v_toFun_6_, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1(lean_object* v_d_10_, lean_object* v_g_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; lean_object* v_toFun_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1___closed__0, &lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1___closed__0_once, _init_lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1___closed__0);
v_toFun_14_ = lean_ctor_get(v___x_13_, 0);
v___f_15_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__0), 3, 2);
lean_closure_set(v___f_15_, 0, v_d_10_);
lean_closure_set(v___f_15_, 1, v_g_11_);
lean_inc(v_toFun_14_);
v___x_16_ = lean_apply_2(v_toFun_14_, v___f_15_, v___y_12_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___redArg(lean_object* v_d_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1), 3, 1);
lean_closure_set(v___f_18_, 0, v_d_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll(lean_object* v_D_19_, lean_object* v_N_20_, lean_object* v_X_21_, lean_object* v_i_22_, lean_object* v_M_23_, lean_object* v_00_u03b9_24_, lean_object* v_d_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_TwSys_delAll___redArg___lam__1), 3, 1);
lean_closure_set(v___f_26_, 0, v_d_25_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_delAll___boxed(lean_object* v_D_27_, lean_object* v_N_28_, lean_object* v_X_29_, lean_object* v_i_30_, lean_object* v_M_31_, lean_object* v_00_u03b9_32_, lean_object* v_d_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_GlobalTheory_TwSys_delAll(v_D_27_, v_N_28_, v_X_29_, v_i_30_, v_M_31_, v_00_u03b9_32_, v_d_33_);
lean_dec(v_M_31_);
lean_dec(v_i_30_);
lean_dec_ref(v_X_29_);
lean_dec_ref(v_N_28_);
lean_dec_ref(v_D_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__0(lean_object* v_algebraMap_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_1(v_algebraMap_35_, v___y_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__1(lean_object* v_00_u03ba_38_, lean_object* v_00_u03c1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_r_43_, lean_object* v_g_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_47_; lean_object* v_val_48_; lean_object* v___x_49_; lean_object* v_val_50_; lean_object* v_algebraMap_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_246__overap_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_inc(v_g_44_);
v___x_47_ = lean_apply_1(v_00_u03ba_38_, v_g_44_);
v_val_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_val_48_);
lean_dec_ref(v___x_47_);
v___x_49_ = lean_apply_1(v_00_u03c1_39_, v_g_44_);
v_val_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v___x_49_);
v_algebraMap_51_ = lean_ctor_get(v_inst_40_, 1);
lean_inc(v_algebraMap_51_);
lean_dec_ref(v_inst_40_);
v___f_52_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_52_, 0, v_algebraMap_51_);
v___x_53_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_map), 8, 6);
lean_closure_set(v___x_53_, 0, lean_box(0));
lean_closure_set(v___x_53_, 1, lean_box(0));
lean_closure_set(v___x_53_, 2, lean_box(0));
lean_closure_set(v___x_53_, 3, lean_box(0));
lean_closure_set(v___x_53_, 4, v_val_50_);
lean_closure_set(v___x_53_, 5, v___f_52_);
lean_inc(v_inst_42_);
v___x_246__overap_54_ = lp_tree_Formalism_MainNotions_BlochKatoReduction_matAct___redArg(v_inst_41_, v_inst_42_, v_r_43_, v___x_53_);
v___x_55_ = lean_apply_2(v___x_246__overap_54_, v___y_45_, v___y_46_);
v___x_56_ = lean_apply_2(v_inst_42_, v_val_48_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___redArg(lean_object* v_inst_57_, lean_object* v_r_58_, lean_object* v_00_u03c1_59_, lean_object* v_00_u03ba_60_, lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___f_63_; 
v___f_63_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__1), 9, 6);
lean_closure_set(v___f_63_, 0, v_00_u03ba_60_);
lean_closure_set(v___f_63_, 1, v_00_u03c1_59_);
lean_closure_set(v___f_63_, 2, v_inst_57_);
lean_closure_set(v___f_63_, 3, v_inst_61_);
lean_closure_set(v___f_63_, 4, v_inst_62_);
lean_closure_set(v___f_63_, 5, v_r_58_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn(lean_object* v_G_64_, lean_object* v_O_65_, lean_object* v_00_u039b_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_r_71_, lean_object* v_00_u03c1_72_, lean_object* v_00_u03ba_73_, lean_object* v_B_74_, lean_object* v_inst_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v___f_77_; 
v___f_77_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_TwSys_repOn___redArg___lam__1), 9, 6);
lean_closure_set(v___f_77_, 0, v_00_u03ba_73_);
lean_closure_set(v___f_77_, 1, v_00_u03c1_72_);
lean_closure_set(v___f_77_, 2, v_inst_70_);
lean_closure_set(v___f_77_, 3, v_inst_75_);
lean_closure_set(v___f_77_, 4, v_inst_76_);
lean_closure_set(v___f_77_, 5, v_r_71_);
return v___f_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_TwSys_repOn___boxed(lean_object* v_G_78_, lean_object* v_O_79_, lean_object* v_00_u039b_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_r_85_, lean_object* v_00_u03c1_86_, lean_object* v_00_u03ba_87_, lean_object* v_B_88_, lean_object* v_inst_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_GlobalTheory_TwSys_repOn(v_G_78_, v_O_79_, v_00_u039b_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_r_85_, v_00_u03c1_86_, v_00_u03ba_87_, v_B_88_, v_inst_89_, v_inst_90_);
lean_dec_ref(v_inst_83_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
return v_res_91_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_IntegralHeckeForms(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTameInertiaElementAtTwistPrime(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_IntegralHeckeForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
