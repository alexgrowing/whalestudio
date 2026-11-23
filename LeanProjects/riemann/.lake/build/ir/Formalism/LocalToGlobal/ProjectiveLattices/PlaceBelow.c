// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_n_x27(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_n_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_q(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_q___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Pj_nnOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_nnOf___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_placeBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_placeBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_n_x27(lean_object* v_Q_1_){
_start:
{
lean_object* v_f_2_; lean_object* v_r_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_f_2_ = lean_ctor_get(v_Q_1_, 6);
v_r_3_ = lean_ctor_get(v_Q_1_, 7);
v___x_4_ = lean_unsigned_to_nat(8u);
v___x_5_ = lean_nat_mul(v___x_4_, v_f_2_);
v___x_6_ = lean_nat_mul(v___x_5_, v_r_3_);
lean_dec(v___x_5_);
v___x_7_ = lean_unsigned_to_nat(4u);
v___x_8_ = lean_nat_add(v___x_6_, v___x_7_);
lean_dec(v___x_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_n_x27___boxed(lean_object* v_Q_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_L2_Pj_DepPage_n_x27(v_Q_9_);
lean_dec_ref(v_Q_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_q(lean_object* v_Q_11_){
_start:
{
lean_object* v_g1_12_; lean_object* v_g2_13_; lean_object* v___x_14_; 
v_g1_12_ = lean_ctor_get(v_Q_11_, 1);
v_g2_13_ = lean_ctor_get(v_Q_11_, 2);
v___x_14_ = lean_nat_mul(v_g1_12_, v_g2_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_DepPage_q___boxed(lean_object* v_Q_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_L2_Pj_DepPage_q(v_Q_15_);
lean_dec_ref(v_Q_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnOf___redArg___lam__0(lean_object* v_pibar_17_, lean_object* v_toNPow_18_, lean_object* v_Dp_19_, lean_object* v_pi_20_, lean_object* v_Dm_21_, lean_object* v_toMul_22_, lean_object* v_i_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_inc(v_i_23_);
v___x_24_ = lean_apply_1(v_pibar_17_, v_i_23_);
lean_inc(v_toNPow_18_);
v___x_25_ = lean_apply_2(v_toNPow_18_, v_Dp_19_, v___x_24_);
v___x_26_ = lean_apply_1(v_pi_20_, v_i_23_);
v___x_27_ = lean_apply_2(v_toNPow_18_, v_Dm_21_, v___x_26_);
v___x_28_ = lean_apply_2(v_toMul_22_, v___x_25_, v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Pj_nnOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = l_List_finRange(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnOf___redArg(lean_object* v_inst_31_, lean_object* v_pi_32_, lean_object* v_pibar_33_, lean_object* v_Dp_34_, lean_object* v_Dm_35_){
_start:
{
lean_object* v___x_36_; lean_object* v_toSemiring_37_; lean_object* v___x_38_; lean_object* v_toMonoid_39_; lean_object* v_toMul_40_; lean_object* v_toNPow_41_; lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___x_44_; 
v___x_36_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_31_);
v_toSemiring_37_ = lean_ctor_get(v_inst_31_, 0);
lean_inc_ref_n(v_toSemiring_37_, 2);
lean_dec_ref(v_inst_31_);
v___x_38_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_37_);
v_toMonoid_39_ = lean_ctor_get(v_toSemiring_37_, 1);
lean_inc_ref(v_toMonoid_39_);
lean_dec_ref(v_toSemiring_37_);
v_toMul_40_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_toMul_40_);
lean_dec_ref(v___x_38_);
v_toNPow_41_ = lean_ctor_get(v_toMonoid_39_, 2);
lean_inc(v_toNPow_41_);
lean_dec_ref(v_toMonoid_39_);
v___x_42_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_nnOf___redArg___closed__0, &lp_tree_Formalism_L2_Pj_nnOf___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Pj_nnOf___redArg___closed__0);
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_nnOf___redArg___lam__0), 7, 6);
lean_closure_set(v___f_43_, 0, v_pibar_33_);
lean_closure_set(v___f_43_, 1, v_toNPow_41_);
lean_closure_set(v___f_43_, 2, v_Dp_34_);
lean_closure_set(v___f_43_, 3, v_pi_32_);
lean_closure_set(v___f_43_, 4, v_Dm_35_);
lean_closure_set(v___f_43_, 5, v_toMul_40_);
v___x_44_ = lp_mathlib_Finset_prod___redArg(v___x_36_, v___x_42_, v___f_43_);
lean_dec_ref(v___x_36_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnOf(lean_object* v_K_45_, lean_object* v_inst_46_, lean_object* v_pi_47_, lean_object* v_pibar_48_, lean_object* v_Dp_49_, lean_object* v_Dm_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_L2_Pj_nnOf___redArg(v_inst_46_, v_pi_47_, v_pibar_48_, v_Dp_49_, v_Dm_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_placeBelow(lean_object* v_K_52_, lean_object* v_inst_53_, lean_object* v_L_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_v_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_placeBelow___boxed(lean_object* v_K_60_, lean_object* v_inst_61_, lean_object* v_L_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_v_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_Formalism_L2_Pj_placeBelow(v_K_60_, v_inst_61_, v_L_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_v_66_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_61_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___redArg___lam__0(lean_object* v_inst_68_, lean_object* v_pi_69_, lean_object* v_i_70_){
_start:
{
lean_object* v_algebraMap_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_algebraMap_71_ = lean_ctor_get(v_inst_68_, 1);
lean_inc(v_algebraMap_71_);
lean_dec_ref(v_inst_68_);
v___x_72_ = lean_apply_1(v_pi_69_, v_i_70_);
v___x_73_ = lean_apply_1(v_algebraMap_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___redArg___lam__1(lean_object* v_inst_74_, lean_object* v_H_75_, lean_object* v_pi_76_, lean_object* v_i_77_){
_start:
{
lean_object* v_bar_78_; lean_object* v_algebraMap_79_; lean_object* v_toFun_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_bar_78_ = lean_ctor_get(v_H_75_, 3);
lean_inc_ref(v_bar_78_);
lean_dec_ref(v_H_75_);
v_algebraMap_79_ = lean_ctor_get(v_inst_74_, 1);
lean_inc(v_algebraMap_79_);
lean_dec_ref(v_inst_74_);
v_toFun_80_ = lean_ctor_get(v_bar_78_, 0);
lean_inc(v_toFun_80_);
lean_dec_ref(v_bar_78_);
v___x_81_ = lean_apply_1(v_pi_76_, v_i_77_);
v___x_82_ = lean_apply_1(v_toFun_80_, v___x_81_);
v___x_83_ = lean_apply_1(v_algebraMap_79_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___redArg(lean_object* v_H_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_D_87_, lean_object* v_j_88_){
_start:
{
lean_object* v_toCommRing_89_; lean_object* v_Dp_90_; lean_object* v_Dm_91_; lean_object* v_pi_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_toCommRing_89_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref(v_toCommRing_89_);
lean_dec_ref(v_inst_85_);
v_Dp_90_ = lean_ctor_get(v_D_87_, 4);
lean_inc_ref(v_Dp_90_);
v_Dm_91_ = lean_ctor_get(v_D_87_, 5);
lean_inc_ref(v_Dm_91_);
v_pi_92_ = lean_ctor_get(v_D_87_, 6);
lean_inc_n(v_pi_92_, 2);
lean_dec_ref(v_D_87_);
lean_inc_ref(v_inst_86_);
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_nnKAt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_93_, 0, v_inst_86_);
lean_closure_set(v___f_93_, 1, v_pi_92_);
v___f_94_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_nnKAt___redArg___lam__1), 4, 3);
lean_closure_set(v___f_94_, 0, v_inst_86_);
lean_closure_set(v___f_94_, 1, v_H_84_);
lean_closure_set(v___f_94_, 2, v_pi_92_);
lean_inc(v_j_88_);
v___x_95_ = lean_apply_1(v_Dp_90_, v_j_88_);
v___x_96_ = lean_apply_1(v_Dm_91_, v_j_88_);
v___x_97_ = lp_tree_Formalism_L2_Pj_nnOf___redArg(v_toCommRing_89_, v___f_93_, v___f_94_, v___x_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt(lean_object* v_E_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_H_102_, lean_object* v_LL_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_D_106_, lean_object* v_j_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lp_tree_Formalism_L2_Pj_nnKAt___redArg(v_H_102_, v_inst_104_, v_inst_105_, v_D_106_, v_j_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_nnKAt___boxed(lean_object* v_E_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_H_113_, lean_object* v_LL_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_D_117_, lean_object* v_j_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_tree_Formalism_L2_Pj_nnKAt(v_E_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_H_113_, v_LL_114_, v_inst_115_, v_inst_116_, v_D_117_, v_j_118_);
lean_dec_ref(v_inst_110_);
return v_res_119_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThProps(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThProps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
