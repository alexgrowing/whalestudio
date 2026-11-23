// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
// Imports: public import Init public meta import Init public import Mathlib public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_yy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_yy_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xn_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xn_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
lean_object* v_a_9_; lean_object* v___x_10_; 
v_a_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_a_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_a_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xm_elim___redArg(lean_object* v_t_23_, lean_object* v_xm_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_23_, v_xm_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xm_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_xm_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_27_, v_xm_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_yy_elim___redArg(lean_object* v_t_31_, lean_object* v_yy_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_31_, v_yy_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_yy_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_yy_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_35_, v_yy_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xn_elim___redArg(lean_object* v_t_39_, lean_object* v_xn_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_39_, v_xn_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_xn_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_xn_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_MdlC_ctorElim___redArg(v_t_43_, v_xn_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___redArg(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_47_) == 1)
{
lean_object* v_snd_49_; lean_object* v_fst_50_; 
v_snd_49_ = lean_ctor_get(v_x_48_, 1);
v_fst_50_ = lean_ctor_get(v_snd_49_, 0);
lean_inc(v_fst_50_);
return v_fst_50_;
}
else
{
lean_object* v_snd_51_; lean_object* v_fst_52_; 
v_snd_51_ = lean_ctor_get(v_x_48_, 1);
v_fst_52_ = lean_ctor_get(v_snd_51_, 0);
lean_inc(v_fst_52_);
return v_fst_52_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___redArg___boxed(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___redArg(v_x_53_, v_x_54_);
lean_dec(v_x_54_);
lean_dec(v_x_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld(lean_object* v_E_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_H_60_, lean_object* v_D_61_, lean_object* v_l_62_, lean_object* v_Xo_63_, lean_object* v_c_64_, lean_object* v_p_65_, lean_object* v_T_66_, lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___redArg(v_x_67_, v_x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld___boxed(lean_object* v_E_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_H_74_, lean_object* v_D_75_, lean_object* v_l_76_, lean_object* v_Xo_77_, lean_object* v_c_78_, lean_object* v_p_79_, lean_object* v_T_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_fld(v_E_70_, v_inst_71_, v_inst_72_, v_inst_73_, v_H_74_, v_D_75_, v_l_76_, v_Xo_77_, v_c_78_, v_p_79_, v_T_80_, v_x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_x_81_);
lean_dec_ref(v_T_80_);
lean_dec(v_p_79_);
lean_dec_ref(v_Xo_77_);
lean_dec_ref(v_l_76_);
lean_dec_ref(v_D_75_);
lean_dec_ref(v_H_74_);
lean_dec_ref(v_inst_71_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm___redArg(lean_object* v_y_84_){
_start:
{
lean_object* v_snd_85_; lean_object* v_snd_86_; lean_object* v_fst_87_; lean_object* v_fst_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_104_; 
v_snd_85_ = lean_ctor_get(v_y_84_, 1);
lean_inc(v_snd_85_);
v_snd_86_ = lean_ctor_get(v_snd_85_, 1);
lean_inc(v_snd_86_);
v_fst_87_ = lean_ctor_get(v_y_84_, 0);
lean_inc(v_fst_87_);
lean_dec_ref(v_y_84_);
v_fst_88_ = lean_ctor_get(v_snd_85_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_snd_85_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_snd_85_, 1);
lean_dec(v_unused_105_);
v___x_90_ = v_snd_85_;
v_isShared_91_ = v_isSharedCheck_104_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_fst_88_);
lean_dec(v_snd_85_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_104_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_fst_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_102_; 
v_fst_92_ = lean_ctor_get(v_snd_86_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_snd_86_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_snd_86_, 1);
lean_dec(v_unused_103_);
v___x_94_ = v_snd_86_;
v_isShared_95_ = v_isSharedCheck_102_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_fst_92_);
lean_dec(v_snd_86_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_102_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_fst_92_);
lean_ctor_set(v___x_94_, 0, v_fst_88_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_fst_88_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_fst_92_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_97_);
lean_ctor_set(v___x_90_, 0, v_fst_87_);
v___x_99_ = v___x_90_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_fst_87_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm(lean_object* v_E_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_H_110_, lean_object* v_D_111_, lean_object* v_l_112_, lean_object* v_Xo_113_, lean_object* v_c_114_, lean_object* v_p_115_, lean_object* v_T_116_, lean_object* v_y_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm___redArg(v_y_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm___boxed(lean_object* v_E_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_H_123_, lean_object* v_D_124_, lean_object* v_l_125_, lean_object* v_Xo_126_, lean_object* v_c_127_, lean_object* v_p_128_, lean_object* v_T_129_, lean_object* v_y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Formalism_L2_Pj_PointsOfFlagModel_toXm(v_E_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_H_123_, v_D_124_, v_l_125_, v_Xo_126_, v_c_127_, v_p_128_, v_T_129_, v_y_130_);
lean_dec_ref(v_T_129_);
lean_dec(v_p_128_);
lean_dec_ref(v_Xo_126_);
lean_dec_ref(v_l_125_);
lean_dec_ref(v_D_124_);
lean_dec_ref(v_H_123_);
lean_dec_ref(v_inst_120_);
return v_res_131_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_IsOpenPart(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_TowerOfAt(uint8_t builtin) {
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
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_IsOpenPart(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
