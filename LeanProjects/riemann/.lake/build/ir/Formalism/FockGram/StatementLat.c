// Lean compiler output
// Module: Formalism.FockGram.StatementLat
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_LinearMap_fst___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_snd___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_LinearMap_compl_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_E_sgram___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_E_sgram___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_bgram___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_bgram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_bgram___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_E_orthSum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_fst___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_E_orthSum___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_E_orthSum___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_E_orthSum___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_snd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_E_orthSum___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_E_orthSum___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram___redArg___lam__0(lean_object* v_v_1_, lean_object* v_B_2_, lean_object* v_i_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_v_1_);
v___x_5_ = lean_apply_1(v_v_1_, v_i_3_);
v___x_6_ = lean_apply_1(v_v_1_, v_j_4_);
v___x_7_ = lean_apply_2(v_B_2_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_lp_tree_Formalism_E_sgram___redArg___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram___redArg(lean_object* v_B_9_, lean_object* v_v_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; lean_object* v_toFun_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&lp_tree_Formalism_E_sgram___redArg___closed__0, &lp_tree_Formalism_E_sgram___redArg___closed__0_once, _init_lp_tree_Formalism_E_sgram___redArg___closed__0);
v_toFun_14_ = lean_ctor_get(v___x_13_, 0);
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_E_sgram___redArg___lam__0), 4, 2);
lean_closure_set(v___f_15_, 0, v_v_10_);
lean_closure_set(v___f_15_, 1, v_B_9_);
lean_inc(v_toFun_14_);
v___x_16_ = lean_apply_3(v_toFun_14_, v___f_15_, v_a_11_, v_a_12_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram(lean_object* v_R_17_, lean_object* v_M_18_, lean_object* v_00_u03b9_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_B_24_, lean_object* v_v_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_E_sgram___redArg(v_B_24_, v_v_25_, v_a_26_, v_a_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_sgram___boxed(lean_object* v_R_29_, lean_object* v_M_30_, lean_object* v_00_u03b9_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_B_36_, lean_object* v_v_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_E_sgram(v_R_29_, v_M_30_, v_00_u03b9_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_B_36_, v_v_37_, v_a_38_, v_a_39_);
lean_dec(v_inst_35_);
lean_dec_ref(v_inst_34_);
lean_dec(v_inst_33_);
lean_dec_ref(v_inst_32_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_bgram___redArg(lean_object* v_B_41_, lean_object* v_v_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_45_; lean_object* v_toFun_46_; lean_object* v___f_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&lp_tree_Formalism_E_sgram___redArg___closed__0, &lp_tree_Formalism_E_sgram___redArg___closed__0_once, _init_lp_tree_Formalism_E_sgram___redArg___closed__0);
v_toFun_46_ = lean_ctor_get(v___x_45_, 0);
v___f_47_ = lean_alloc_closure((void*)(lp_tree_Formalism_E_sgram___redArg___lam__0), 4, 2);
lean_closure_set(v___f_47_, 0, v_v_42_);
lean_closure_set(v___f_47_, 1, v_B_41_);
lean_inc(v_toFun_46_);
v___x_48_ = lean_apply_3(v_toFun_46_, v___f_47_, v_a_43_, v_a_44_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_bgram(lean_object* v_R_49_, lean_object* v_M_50_, lean_object* v_00_u03b9_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_B_55_, lean_object* v_v_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_E_bgram___redArg(v_B_55_, v_v_56_, v_a_57_, v_a_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_bgram___boxed(lean_object* v_R_60_, lean_object* v_M_61_, lean_object* v_00_u03b9_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_B_66_, lean_object* v_v_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_E_bgram(v_R_60_, v_M_61_, v_00_u03b9_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_B_66_, v_v_67_, v_a_68_, v_a_69_);
lean_dec(v_inst_65_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum___redArg___lam__0(lean_object* v_toAddCommMonoid_71_, lean_object* v___f_72_, lean_object* v___f_73_, lean_object* v___f_74_, lean_object* v___f_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_toAddSemigroup_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_toAddSemigroup_78_ = lean_ctor_get(v_toAddCommMonoid_71_, 0);
lean_inc(v_toAddSemigroup_78_);
lean_dec_ref(v_toAddCommMonoid_71_);
lean_inc_ref(v___y_77_);
lean_inc_ref(v___y_76_);
v___x_79_ = lp_mathlib_LinearMap_compl_u2082___redArg___lam__0(v___f_72_, v___f_73_, v___y_76_, v___y_77_);
v___x_80_ = lp_mathlib_LinearMap_compl_u2082___redArg___lam__0(v___f_74_, v___f_75_, v___y_76_, v___y_77_);
v___x_81_ = lean_apply_2(v_toAddSemigroup_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum___redArg(lean_object* v_inst_84_, lean_object* v_B_u2081_85_, lean_object* v_B_u2082_86_){
_start:
{
lean_object* v_toAddCommMonoid_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; 
v_toAddCommMonoid_87_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_ref(v_toAddCommMonoid_87_);
lean_dec_ref(v_inst_84_);
v___f_88_ = ((lean_object*)(lp_tree_Formalism_E_orthSum___redArg___closed__0));
v___f_89_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_89_, 0, v___f_88_);
lean_closure_set(v___f_89_, 1, v_B_u2081_85_);
v___f_90_ = ((lean_object*)(lp_tree_Formalism_E_orthSum___redArg___closed__1));
v___f_91_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v___f_90_);
lean_closure_set(v___f_91_, 1, v_B_u2082_86_);
v___f_92_ = lean_alloc_closure((void*)(lp_tree_Formalism_E_orthSum___redArg___lam__0), 7, 5);
lean_closure_set(v___f_92_, 0, v_toAddCommMonoid_87_);
lean_closure_set(v___f_92_, 1, v___f_89_);
lean_closure_set(v___f_92_, 2, v___f_88_);
lean_closure_set(v___f_92_, 3, v___f_91_);
lean_closure_set(v___f_92_, 4, v___f_90_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum(lean_object* v_R_93_, lean_object* v_M_u2081_94_, lean_object* v_M_u2082_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_B_u2081_102_, lean_object* v_B_u2082_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_tree_Formalism_E_orthSum___redArg(v_inst_96_, v_B_u2081_102_, v_B_u2082_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_orthSum___boxed(lean_object* v_R_105_, lean_object* v_M_u2081_106_, lean_object* v_M_u2082_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_B_u2081_114_, lean_object* v_B_u2082_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_tree_Formalism_E_orthSum(v_R_105_, v_M_u2081_106_, v_M_u2082_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_B_u2081_114_, v_B_u2082_115_);
lean_dec(v_inst_113_);
lean_dec_ref(v_inst_112_);
lean_dec(v_inst_111_);
lean_dec_ref(v_inst_110_);
lean_dec(v_inst_109_);
return v_res_116_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FockGram_StatementLat(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
