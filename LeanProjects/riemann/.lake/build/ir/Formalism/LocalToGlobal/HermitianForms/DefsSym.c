// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.DefsSym
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_rSym(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_rSym___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_posSym(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_posSym___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lvSym(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lvSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_JSymG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_JSymG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_insB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_insB___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_rSym(lean_object* v_k_1_, lean_object* v_rS_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_mul(v___x_3_, v_rS_2_);
v___x_5_ = lean_nat_add(v_k_1_, v___x_4_);
lean_dec(v___x_4_);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_add(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_rSym___boxed(lean_object* v_k_8_, lean_object* v_rS_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_L2_Forms_rSym(v_k_8_, v_rS_9_);
lean_dec(v_rS_9_);
lean_dec(v_k_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_posSym(lean_object* v_k_11_, lean_object* v_rS_12_, lean_object* v_x_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_lt(v_x_13_, v_k_11_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_nat_sub(v_x_13_, v_k_11_);
v___x_16_ = lean_nat_dec_lt(v___x_15_, v_rS_12_);
if (v___x_16_ == 0)
{
lean_dec(v___x_15_);
lean_inc(v_x_13_);
return v_x_13_;
}
else
{
return v___x_15_;
}
}
else
{
lean_object* v___x_17_; 
v___x_17_ = lean_nat_add(v_rS_12_, v_x_13_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_posSym___boxed(lean_object* v_k_18_, lean_object* v_rS_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_Forms_posSym(v_k_18_, v_rS_19_, v_x_20_);
lean_dec(v_x_20_);
lean_dec(v_rS_19_);
lean_dec(v_k_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lvSym(lean_object* v_k_22_, lean_object* v_rS_23_, lean_object* v_t_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lp_tree_Formalism_L2_Forms_rSym(v_k_22_, v_rS_23_);
v___x_27_ = lean_nat_dec_lt(v_x_25_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_nat_sub(v_x_25_, v___x_26_);
v___x_29_ = lean_nat_div(v___x_28_, v_t_24_);
lean_dec(v___x_28_);
v___x_30_ = lean_nat_add(v___x_26_, v___x_29_);
lean_dec(v___x_29_);
lean_dec(v___x_26_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; 
lean_dec(v___x_26_);
v___x_31_ = lp_tree_Formalism_L2_Forms_posSym(v_k_22_, v_rS_23_, v_x_25_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_lvSym___boxed(lean_object* v_k_32_, lean_object* v_rS_33_, lean_object* v_t_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_L2_Forms_lvSym(v_k_32_, v_rS_33_, v_t_34_, v_x_35_);
lean_dec(v_x_35_);
lean_dec(v_t_34_);
lean_dec(v_rS_33_);
lean_dec(v_k_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_JSymG(lean_object* v_00_u03ba_37_, lean_object* v_inst_38_, lean_object* v_n_39_, lean_object* v_k_40_, lean_object* v_rS_41_, lean_object* v_t_42_, uint8_t v_zl_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_JSymG___boxed(lean_object* v_00_u03ba_45_, lean_object* v_inst_46_, lean_object* v_n_47_, lean_object* v_k_48_, lean_object* v_rS_49_, lean_object* v_t_50_, lean_object* v_zl_51_){
_start:
{
uint8_t v_zl_boxed_52_; lean_object* v_res_53_; 
v_zl_boxed_52_ = lean_unbox(v_zl_51_);
v_res_53_ = lp_tree_Formalism_L2_Forms_JSymG(v_00_u03ba_45_, v_inst_46_, v_n_47_, v_k_48_, v_rS_49_, v_t_50_, v_zl_boxed_52_);
lean_dec(v_t_50_);
lean_dec(v_rS_49_);
lean_dec(v_k_48_);
lean_dec(v_n_47_);
lean_dec_ref(v_inst_46_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_insB(lean_object* v_k_54_, lean_object* v_c_55_, lean_object* v_x_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_lt(v_x_56_, v_k_54_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_nat_add(v_x_56_, v_c_55_);
return v___x_58_;
}
else
{
lean_inc(v_x_56_);
return v_x_56_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_insB___boxed(lean_object* v_k_59_, lean_object* v_c_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_L2_Forms_insB(v_k_59_, v_c_60_, v_x_61_);
lean_dec(v_x_61_);
lean_dec(v_c_60_);
lean_dec(v_k_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__0(lean_object* v_k_63_, lean_object* v_c_64_, lean_object* v_x_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lp_tree_Formalism_L2_Forms_insB(v_k_63_, v_c_64_, v_x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__0___boxed(lean_object* v_k_67_, lean_object* v_c_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_L2_Forms_eBf___redArg___lam__0(v_k_67_, v_c_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_c_68_);
lean_dec(v_k_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__1(lean_object* v_k_71_, lean_object* v_i_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_nat_add(v_k_71_, v_i_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg___lam__1___boxed(lean_object* v_k_74_, lean_object* v_i_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_L2_Forms_eBf___redArg___lam__1(v_k_74_, v_i_75_);
lean_dec(v_i_75_);
lean_dec(v_k_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___redArg(lean_object* v_k_77_, lean_object* v_c_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___x_82_; 
lean_inc(v_k_77_);
v___f_80_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_eBf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_80_, 0, v_k_77_);
lean_closure_set(v___f_80_, 1, v_c_78_);
v___f_81_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_eBf___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_81_, 0, v_k_77_);
v___x_82_ = l_Sum_elim___redArg(v___f_80_, v___f_81_, v_a_79_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf(lean_object* v_N_83_, lean_object* v_k_84_, lean_object* v_c_85_, lean_object* v_hk_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_tree_Formalism_L2_Forms_eBf___redArg(v_k_84_, v_c_85_, v_a_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_eBf___boxed(lean_object* v_N_89_, lean_object* v_k_90_, lean_object* v_c_91_, lean_object* v_hk_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_tree_Formalism_L2_Forms_eBf(v_N_89_, v_k_90_, v_c_91_, v_hk_92_, v_a_93_);
lean_dec(v_N_89_);
return v_res_94_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_PsiZeroNontrivialCharacter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_DefsSym(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_PsiZeroNontrivialCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
