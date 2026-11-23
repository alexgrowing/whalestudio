// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementN public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
uint8_t lp_mathlib_Fintype_decidableEqEquivFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_instFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___closed__0;
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__0(lean_object* v_n_1_, lean_object* v_s_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_5_, 0, v_n_1_);
lean_inc(v_a_4_);
v___x_6_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_5_, v_a_4_, v_s_2_);
if (v___x_6_ == 0)
{
lean_object* v_toFun_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_toFun_7_ = lean_ctor_get(v_a_3_, 0);
lean_inc(v_toFun_7_);
lean_dec_ref(v_a_3_);
lean_inc(v_a_4_);
v___x_8_ = lean_apply_1(v_toFun_7_, v_a_4_);
v___x_9_ = lean_nat_dec_eq(v___x_8_, v_a_4_);
lean_dec(v_a_4_);
lean_dec(v___x_8_);
return v___x_9_;
}
else
{
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__0___boxed(lean_object* v_n_10_, lean_object* v_s_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__0(v_n_10_, v_s_11_, v_a_12_, v_a_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
static lean_object* _init_lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___closed__0(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1(lean_object* v_n_17_, lean_object* v___x_18_, lean_object* v_s_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
lean_inc(v_n_17_);
v___x_21_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_21_, 0, v_n_17_);
lean_inc_ref_n(v_a_20_, 2);
v___x_22_ = lp_mathlib_Equiv_trans___redArg(v_a_20_, v_a_20_);
v___x_23_ = lean_obj_once(&lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___closed__0, &lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___closed__0_once, _init_lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___closed__0);
v___x_24_ = lp_mathlib_Fintype_decidableEqEquivFintype___redArg(v___x_21_, v___x_18_, v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
lean_dec_ref(v_a_20_);
lean_dec(v_s_19_);
lean_dec(v_n_17_);
return v___x_24_;
}
else
{
lean_object* v___f_25_; uint8_t v___x_26_; 
lean_inc(v_n_17_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_25_, 0, v_n_17_);
lean_closure_set(v___f_25_, 1, v_s_19_);
lean_closure_set(v___f_25_, 2, v_a_20_);
v___x_26_ = l_Nat_decidableForallFin___redArg(v_n_17_, v___f_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___boxed(lean_object* v_n_27_, lean_object* v___x_28_, lean_object* v_s_29_, lean_object* v_a_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1(v_n_27_, v___x_28_, v_s_29_, v_a_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_invOn(lean_object* v_n_33_, lean_object* v_s_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc_n(v_n_33_, 2);
v___x_35_ = l_List_finRange(v_n_33_);
lean_inc_n(v___x_35_, 2);
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_invOn___lam__1___boxed), 4, 3);
lean_closure_set(v___f_36_, 0, v_n_33_);
lean_closure_set(v___f_36_, 1, v___x_35_);
lean_closure_set(v___f_36_, 2, v_s_34_);
v___x_37_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_37_, 0, v_n_33_);
lean_inc_ref(v___x_37_);
v___x_38_ = lp_mathlib_Equiv_instFintype___redArg(v___x_37_, v___x_37_, v___x_35_, v___x_35_);
v___x_39_ = lp_mathlib_Multiset_filter___redArg(v___f_36_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__0(lean_object* v_00_u03c3_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_toFun_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_toFun_42_ = lean_ctor_get(v_00_u03c3_40_, 0);
lean_inc(v_toFun_42_);
lean_dec_ref(v_00_u03c3_40_);
lean_inc(v_a_41_);
v___x_43_ = lean_apply_1(v_toFun_42_, v_a_41_);
v___x_44_ = lean_nat_dec_lt(v_a_41_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v_a_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__0___boxed(lean_object* v_00_u03c3_45_, lean_object* v_a_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__0(v_00_u03c3_45_, v_a_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__1(lean_object* v_00_u03c3_49_, lean_object* v_w_50_, lean_object* v_i_51_){
_start:
{
lean_object* v_toFun_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_toFun_52_ = lean_ctor_get(v_00_u03c3_49_, 0);
lean_inc(v_toFun_52_);
lean_dec_ref(v_00_u03c3_49_);
lean_inc(v_i_51_);
v___x_53_ = lean_apply_1(v_toFun_52_, v_i_51_);
v___x_54_ = lean_apply_2(v_w_50_, v_i_51_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg(lean_object* v_n_55_, lean_object* v_inst_56_, lean_object* v_w_57_, lean_object* v_00_u03c3_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_inc_ref(v_00_u03c3_58_);
v___f_59_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_59_, 0, v_00_u03c3_58_);
v___f_60_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___lam__1), 3, 2);
lean_closure_set(v___f_60_, 0, v_00_u03c3_58_);
lean_closure_set(v___f_60_, 1, v_w_57_);
v___x_61_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_56_);
v___x_62_ = l_List_finRange(v_n_55_);
v___x_63_ = lp_mathlib_Multiset_filter___redArg(v___f_59_, v___x_62_);
v___x_64_ = lp_mathlib_Finset_prod___redArg(v___x_61_, v___x_63_, v___f_60_);
lean_dec_ref(v___x_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg___boxed(lean_object* v_n_65_, lean_object* v_inst_66_, lean_object* v_w_67_, lean_object* v_00_u03c3_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg(v_n_65_, v_inst_66_, v_w_67_, v_00_u03c3_68_);
lean_dec_ref(v_inst_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW(lean_object* v_n_70_, lean_object* v_R_71_, lean_object* v_inst_72_, lean_object* v_w_73_, lean_object* v_00_u03c3_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___redArg(v_n_70_, v_inst_72_, v_w_73_, v_00_u03c3_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_edgeW___boxed(lean_object* v_n_76_, lean_object* v_R_77_, lean_object* v_inst_78_, lean_object* v_w_79_, lean_object* v_00_u03c3_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_Formalism_DworkPowerSeriesWeights_edgeW(v_n_76_, v_R_77_, v_inst_78_, v_w_79_, v_00_u03c3_80_);
lean_dec_ref(v_inst_78_);
return v_res_81_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementN(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP(uint8_t builtin);
lean_object* initialize_tree_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
