// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.NumbersLemmas
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Divisibility.Numbers public import Formalism.LocalRingCardinality.DataForced public import Formalism.LocalRingCardinality.DataKap public import Formalism.LocalRingCardinality.DataErr public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries public import Formalism.LocalRingCardinality.HostCls public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
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
lean_object* lp_tree_Formalism_BasicNotions_tauPl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ofRecord___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ofRecord(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ofRecord___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_letterOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_letterOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_letterOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_letterOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_codeOf___lam__0(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_codeOf___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_codeOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_codeOf___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_codeOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_codeOf___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_codeOf___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_codeOf___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_codeOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ofRecord___lam__0(lean_object* v_D_1_, lean_object* v_hc_2_, lean_object* v_z_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lp_tree_Formalism_BasicNotions_tauPl(v_D_1_, v_z_3_);
v___x_5_ = lean_apply_1(v_hc_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ofRecord(lean_object* v_D_6_, lean_object* v_L_7_, lean_object* v_Del_8_, lean_object* v_h0_9_){
_start:
{
lean_object* v_host_10_; lean_object* v_R_11_; lean_object* v_hc_12_; lean_object* v_sc_13_; lean_object* v_toHostAx_14_; lean_object* v_g_15_; lean_object* v_TT_16_; lean_object* v___f_17_; lean_object* v___x_18_; 
v_host_10_ = lean_ctor_get(v_D_6_, 1);
v_R_11_ = lean_ctor_get(v_D_6_, 0);
lean_inc_ref(v_R_11_);
v_hc_12_ = lean_ctor_get(v_D_6_, 6);
lean_inc_ref(v_hc_12_);
v_sc_13_ = lean_ctor_get(v_L_7_, 0);
v_toHostAx_14_ = lean_ctor_get(v_host_10_, 0);
lean_inc_ref(v_toHostAx_14_);
v_g_15_ = lean_ctor_get(v_host_10_, 6);
lean_inc_ref(v_g_15_);
v_TT_16_ = lean_ctor_get(v_host_10_, 10);
lean_inc(v_TT_16_);
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_ofRecord___lam__0), 3, 2);
lean_closure_set(v___f_17_, 0, v_D_6_);
lean_closure_set(v___f_17_, 1, v_hc_12_);
lean_inc_ref(v_sc_13_);
v___x_18_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_18_, 0, v_R_11_);
lean_ctor_set(v___x_18_, 1, v_sc_13_);
lean_ctor_set(v___x_18_, 2, v_toHostAx_14_);
lean_ctor_set(v___x_18_, 3, v_g_15_);
lean_ctor_set(v___x_18_, 4, v_TT_16_);
lean_ctor_set(v___x_18_, 5, v_Del_8_);
lean_ctor_set(v___x_18_, 6, v_h0_9_);
lean_ctor_set(v___x_18_, 7, v___f_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ofRecord___boxed(lean_object* v_D_19_, lean_object* v_L_20_, lean_object* v_Del_21_, lean_object* v_h0_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_DIV_ofRecord(v_D_19_, v_L_20_, v_Del_21_, v_h0_22_);
lean_dec_ref(v_L_20_);
return v_res_23_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_letterOf___redArg(lean_object* v_D_24_, lean_object* v_u_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_s_27_; lean_object* v_letter_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_s_27_ = lean_ctor_get(v_D_24_, 35);
lean_inc_ref(v_s_27_);
lean_dec_ref(v_D_24_);
v_letter_28_ = lean_ctor_get(v_s_27_, 2);
lean_inc_ref(v_letter_28_);
lean_dec_ref(v_s_27_);
v___x_29_ = lean_apply_2(v_letter_28_, v_u_25_, v_a_26_);
v___x_30_ = lean_unbox(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_letterOf___redArg___boxed(lean_object* v_D_31_, lean_object* v_u_32_, lean_object* v_a_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = lp_tree_Formalism_L2_DIV_letterOf___redArg(v_D_31_, v_u_32_, v_a_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_letterOf(lean_object* v_D_36_, lean_object* v_L_37_, lean_object* v_Del_38_, lean_object* v_h0_39_, lean_object* v_u_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_s_42_; lean_object* v_letter_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_s_42_ = lean_ctor_get(v_D_36_, 35);
lean_inc_ref(v_s_42_);
lean_dec_ref(v_D_36_);
v_letter_43_ = lean_ctor_get(v_s_42_, 2);
lean_inc_ref(v_letter_43_);
lean_dec_ref(v_s_42_);
v___x_44_ = lean_apply_2(v_letter_43_, v_u_40_, v_a_41_);
v___x_45_ = lean_unbox(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_letterOf___boxed(lean_object* v_D_46_, lean_object* v_L_47_, lean_object* v_Del_48_, lean_object* v_h0_49_, lean_object* v_u_50_, lean_object* v_a_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = lp_tree_Formalism_L2_DIV_letterOf(v_D_46_, v_L_47_, v_Del_48_, v_h0_49_, v_u_50_, v_a_51_);
lean_dec(v_h0_49_);
lean_dec(v_Del_48_);
lean_dec_ref(v_L_47_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_codeOf___lam__0(lean_object* v_a_54_, uint8_t v___y_55_, uint8_t v___y_56_){
_start:
{
if (v___y_55_ == 0)
{
if (v___y_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = 1;
return v___x_57_;
}
else
{
return v___y_55_;
}
}
else
{
return v___y_56_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_codeOf___lam__0___boxed(lean_object* v_a_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
uint8_t v___y_58__boxed_61_; uint8_t v___y_59__boxed_62_; uint8_t v_res_63_; lean_object* v_r_64_; 
v___y_58__boxed_61_ = lean_unbox(v___y_59_);
v___y_59__boxed_62_ = lean_unbox(v___y_60_);
v_res_63_ = lp_tree_Formalism_L2_DIV_codeOf___lam__0(v_a_58_, v___y_58__boxed_61_, v___y_59__boxed_62_);
lean_dec(v_a_58_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_codeOf___lam__1(lean_object* v_R_65_, lean_object* v___f_66_, lean_object* v_a_67_, lean_object* v_b_68_){
_start:
{
lean_object* v_k_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_k_69_ = lean_ctor_get(v_R_65_, 1);
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = lean_nat_sub(v_k_69_, v___x_70_);
v___x_72_ = l_List_finRange(v___x_71_);
v___x_73_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_66_, v___x_72_, v_a_67_, v_b_68_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_codeOf___lam__1___boxed(lean_object* v_R_74_, lean_object* v___f_75_, lean_object* v_a_76_, lean_object* v_b_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = lp_tree_Formalism_L2_DIV_codeOf___lam__1(v_R_74_, v___f_75_, v_a_76_, v_b_77_);
lean_dec_ref(v_R_74_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_codeOf(lean_object* v_D_81_, lean_object* v_L_82_, lean_object* v_Del_83_, lean_object* v_h0_84_){
_start:
{
lean_object* v_R_85_; lean_object* v_wordFin_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_R_85_ = lean_ctor_get(v_D_81_, 0);
v_wordFin_86_ = lean_ctor_get(v_D_81_, 7);
lean_inc(v_wordFin_86_);
v___f_87_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_codeOf___closed__0));
lean_inc_ref(v_R_85_);
v___f_88_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_codeOf___lam__1___boxed), 4, 2);
lean_closure_set(v___f_88_, 0, v_R_85_);
lean_closure_set(v___f_88_, 1, v___f_87_);
v___x_89_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_letterOf___boxed), 6, 4);
lean_closure_set(v___x_89_, 0, v_D_81_);
lean_closure_set(v___x_89_, 1, v_L_82_);
lean_closure_set(v___x_89_, 2, v_Del_83_);
lean_closure_set(v___x_89_, 3, v_h0_84_);
v___x_90_ = lp_mathlib_Finset_image___redArg(v___f_88_, v___x_89_, v_wordFin_86_);
return v___x_90_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Numbers(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForced(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKap(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataErr(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleWeightMiddleEntries(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_HostCls(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_NonemptyFieldAxiomsCyclicPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_NumbersLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Numbers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataForced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleWeightMiddleEntries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_HostCls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_NonemptyFieldAxiomsCyclicPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
