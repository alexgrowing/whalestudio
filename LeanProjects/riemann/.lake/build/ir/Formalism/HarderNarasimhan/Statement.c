// Lean compiler output
// Module: Formalism.HarderNarasimhan.Statement
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LatticeSlopes.Statement
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
lean_object* lp_mathlib_AddSubgroup_toIntSubmodule___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_toEmbedding___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(lean_object*);
lean_object* lp_mathlib_Pi_evalMulHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_WithLp_linearEquiv___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_instFunLike___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_MulHom_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_zl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_zl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_zl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_hnStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_hnStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HN_piReal___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HN_piReal___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_zl___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v_toAddCommGroup_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_toAddCommGroup_2_ = lean_ctor_get(v_inst_1_, 1);
lean_inc_ref(v_toAddCommGroup_2_);
lean_dec_ref(v_inst_1_);
v___x_3_ = lp_mathlib_AddSubgroup_toIntSubmodule___redArg(v_toAddCommGroup_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lp_mathlib_Equiv_toEmbedding___redArg___lam__0(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_zl(lean_object* v_R_6_, lean_object* v_inst_7_, lean_object* v_V_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_E_11_, lean_object* v_inst_12_, lean_object* v_00_u03c1_13_, lean_object* v_N_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_tree_Formalism_HN_zl___redArg(v_inst_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_zl___boxed(lean_object* v_R_16_, lean_object* v_inst_17_, lean_object* v_V_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_E_21_, lean_object* v_inst_22_, lean_object* v_00_u03c1_23_, lean_object* v_N_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_HN_zl(v_R_16_, v_inst_17_, v_V_18_, v_inst_19_, v_inst_20_, v_E_21_, v_inst_22_, v_00_u03c1_23_, v_N_24_);
lean_dec(v_00_u03c1_23_);
lean_dec(v_inst_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_17_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_hnStep(lean_object* v_R_26_, lean_object* v_inst_27_, lean_object* v_V_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_E_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_00_u03c1_35_, lean_object* v_L_36_, lean_object* v_00_u03b8_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_hnStep___boxed(lean_object* v_R_39_, lean_object* v_inst_40_, lean_object* v_V_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_E_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_00_u03c1_48_, lean_object* v_L_49_, lean_object* v_00_u03b8_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_Formalism_HN_hnStep(v_R_39_, v_inst_40_, v_V_41_, v_inst_42_, v_inst_43_, v_E_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_00_u03c1_48_, v_L_49_, v_00_u03b8_50_);
lean_dec(v_00_u03b8_50_);
lean_dec(v_00_u03c1_48_);
lean_dec_ref(v_inst_46_);
lean_dec_ref(v_inst_45_);
lean_dec(v_inst_43_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_40_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___redArg___lam__0(lean_object* v_inst_52_, lean_object* v_i_53_){
_start:
{
lean_object* v___x_54_; lean_object* v_toAddCommGroup_55_; 
v___x_54_ = lean_apply_1(v_inst_52_, v_i_53_);
v_toAddCommGroup_55_ = lean_ctor_get(v___x_54_, 1);
lean_inc_ref(v_toAddCommGroup_55_);
lean_dec_ref(v___x_54_);
return v_toAddCommGroup_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___redArg___lam__1(lean_object* v_00_u03c1_56_, lean_object* v_i_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
lean_inc(v_i_57_);
v___x_59_ = lean_apply_1(v_00_u03c1_56_, v_i_57_);
v___f_60_ = lean_alloc_closure((void*)(lp_mathlib_Pi_evalMulHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_60_, 0, v_i_57_);
v___x_61_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_60_, v___x_59_, v___y_58_);
return v___x_61_;
}
}
static lean_object* _init_lp_tree_Formalism_HN_piReal___redArg___closed__0(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(2u);
v___x_63_ = lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___redArg(lean_object* v_inst_64_, lean_object* v_00_u03c1_65_){
_start:
{
lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_toLinearMap_71_; lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___f_75_; 
v___f_66_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_piReal___redArg___lam__0), 2, 1);
lean_closure_set(v___f_66_, 0, v_inst_64_);
v___x_67_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_66_);
v___x_68_ = lean_obj_once(&lp_tree_Formalism_HN_piReal___redArg___closed__0, &lp_tree_Formalism_HN_piReal___redArg___closed__0_once, _init_lp_tree_Formalism_HN_piReal___redArg___closed__0);
v___x_69_ = lp_mathlib_WithLp_linearEquiv___redArg(v___x_68_, v___x_67_);
lean_dec_ref(v___x_67_);
v___x_70_ = lp_mathlib_LinearEquiv_symm___redArg(v___x_69_);
v_toLinearMap_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_toLinearMap_71_);
lean_dec_ref(v___x_70_);
v___f_72_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_piReal___redArg___lam__1), 3, 1);
lean_closure_set(v___f_72_, 0, v_00_u03c1_65_);
v___f_73_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instFunLike___lam__0), 2, 1);
lean_closure_set(v___f_73_, 0, v_toLinearMap_71_);
v___f_74_ = lean_alloc_closure((void*)(lp_mathlib_MulHom_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_74_, 0, v___f_72_);
v___f_75_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_75_, 0, v___f_74_);
lean_closure_set(v___f_75_, 1, v___f_73_);
return v___f_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal(lean_object* v_00_u03b9_76_, lean_object* v_inst_77_, lean_object* v_V_78_, lean_object* v_inst_79_, lean_object* v_E_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_00_u03c1_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_tree_Formalism_HN_piReal___redArg(v_inst_81_, v_00_u03c1_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piReal___boxed(lean_object* v_00_u03b9_85_, lean_object* v_inst_86_, lean_object* v_V_87_, lean_object* v_inst_88_, lean_object* v_E_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_00_u03c1_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_Formalism_HN_piReal(v_00_u03b9_85_, v_inst_86_, v_V_87_, v_inst_88_, v_E_89_, v_inst_90_, v_inst_91_, v_00_u03c1_92_);
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_inst_88_);
lean_dec(v_inst_86_);
return v_res_93_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HarderNarasimhan_Statement(uint8_t builtin) {
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
res = initialize_tree_Formalism_LatticeSlopes_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
