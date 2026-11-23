// Lean compiler output
// Module: Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
// Imports: public import Init public meta import Init public import Formalism.HarderNarasimhan.DefsPl
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
lean_object* lp_mathlib_WithLp_equiv(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_v_2_, lean_object* v_w_3_, lean_object* v_p_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_fst_5_ = lean_ctor_get(v_p_4_, 0);
lean_inc(v_fst_5_);
v___x_6_ = lean_apply_2(v_inst_1_, v_fst_5_, v_v_2_);
v___x_7_ = lean_unbox(v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec_ref(v_p_4_);
lean_dec(v_w_3_);
v___x_8_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_1(v_w_3_, v_p_4_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__1(lean_object* v___x_10_, lean_object* v_inst_11_, lean_object* v_v_12_, lean_object* v_w_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toFun_17_; lean_object* v___f_18_; lean_object* v___x_19_; 
v___x_15_ = lp_mathlib_WithLp_equiv(v___x_10_, lean_box(0));
v___x_16_ = lp_mathlib_Equiv_symm___redArg(v___x_15_);
v_toFun_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_toFun_17_);
lean_dec_ref(v___x_16_);
v___f_18_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__0), 4, 3);
lean_closure_set(v___f_18_, 0, v_inst_11_);
lean_closure_set(v___f_18_, 1, v_v_12_);
lean_closure_set(v___f_18_, 2, v_w_13_);
v___x_19_ = lean_apply_2(v_toFun_17_, v___f_18_, v___y_14_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__1___boxed(lean_object* v___x_20_, lean_object* v_inst_21_, lean_object* v_v_22_, lean_object* v_w_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__1(v___x_20_, v_inst_21_, v_v_22_, v_w_23_, v___y_24_);
lean_dec(v___x_20_);
return v_res_25_;
}
}
static lean_object* _init_lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(2u);
v___x_27_ = lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg(lean_object* v_inst_28_, lean_object* v_v_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___f_31_; 
v___x_30_ = lean_obj_once(&lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0, &lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0_once, _init_lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0);
v___f_31_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_31_, 0, v___x_30_);
lean_closure_set(v___f_31_, 1, v_inst_28_);
lean_closure_set(v___f_31_, 2, v_v_29_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_prj(lean_object* v_P_32_, lean_object* v_00_u03b9_33_, lean_object* v_inst_34_, lean_object* v_v_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg(v_inst_34_, v_v_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__0(lean_object* v_inst_37_, lean_object* v_v_38_, lean_object* v___x_39_, lean_object* v_z_40_, lean_object* v_p_41_){
_start:
{
lean_object* v_fst_42_; lean_object* v_snd_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_fst_42_ = lean_ctor_get(v_p_41_, 0);
lean_inc(v_fst_42_);
v_snd_43_ = lean_ctor_get(v_p_41_, 1);
lean_inc(v_snd_43_);
lean_dec_ref(v_p_41_);
v___x_44_ = lean_apply_2(v_inst_37_, v_fst_42_, v_v_38_);
v___x_45_ = lean_unbox(v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec(v_snd_43_);
lean_dec_ref(v_z_40_);
v___x_46_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_46_;
}
else
{
lean_object* v_fst_47_; lean_object* v_snd_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_fst_47_ = lean_ctor_get(v_snd_43_, 0);
lean_inc(v_fst_47_);
v_snd_48_ = lean_ctor_get(v_snd_43_, 1);
lean_inc(v_snd_48_);
lean_dec(v_snd_43_);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_nat_mod(v___x_49_, v___x_39_);
v___x_51_ = lean_nat_dec_eq(v_snd_48_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v_snd_48_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v_im_53_; 
v___x_52_ = lean_apply_1(v_z_40_, v_fst_47_);
v_im_53_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_im_53_);
lean_dec_ref(v___x_52_);
return v_im_53_;
}
else
{
lean_object* v___x_54_; lean_object* v_re_55_; 
v___x_54_ = lean_apply_1(v_z_40_, v_fst_47_);
v_re_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_re_55_);
lean_dec_ref(v___x_54_);
return v_re_55_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__0___boxed(lean_object* v_inst_56_, lean_object* v_v_57_, lean_object* v___x_58_, lean_object* v_z_59_, lean_object* v_p_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__0(v_inst_56_, v_v_57_, v___x_58_, v_z_59_, v_p_60_);
lean_dec(v___x_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__1(lean_object* v___x_62_, lean_object* v_inst_63_, lean_object* v_v_64_, lean_object* v___x_65_, lean_object* v_z_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_toFun_70_; lean_object* v___f_71_; lean_object* v___x_72_; 
v___x_68_ = lp_mathlib_WithLp_equiv(v___x_62_, lean_box(0));
v___x_69_ = lp_mathlib_Equiv_symm___redArg(v___x_68_);
v_toFun_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_toFun_70_);
lean_dec_ref(v___x_69_);
v___f_71_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_71_, 0, v_inst_63_);
lean_closure_set(v___f_71_, 1, v_v_64_);
lean_closure_set(v___f_71_, 2, v___x_65_);
lean_closure_set(v___f_71_, 3, v_z_66_);
v___x_72_ = lean_apply_2(v_toFun_70_, v___f_71_, v___y_67_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__1___boxed(lean_object* v___x_73_, lean_object* v_inst_74_, lean_object* v_v_75_, lean_object* v___x_76_, lean_object* v_z_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__1(v___x_73_, v_inst_74_, v_v_75_, v___x_76_, v_z_77_, v___y_78_);
lean_dec(v___x_73_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg(lean_object* v_inst_80_, lean_object* v_v_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; 
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = lean_obj_once(&lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0, &lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0_once, _init_lp_tree_Formalism_HN_PlaceDecomposition_prj___redArg___closed__0);
v___f_84_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_84_, 0, v___x_83_);
lean_closure_set(v___f_84_, 1, v_inst_80_);
lean_closure_set(v___f_84_, 2, v_v_81_);
lean_closure_set(v___f_84_, 3, v___x_82_);
return v___f_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_PlaceDecomposition_psi(lean_object* v_P_85_, lean_object* v_00_u03b9_86_, lean_object* v_inst_87_, lean_object* v_v_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_tree_Formalism_HN_PlaceDecomposition_psi___redArg(v_inst_87_, v_v_88_);
return v___x_89_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_DefsPl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_DefsPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
