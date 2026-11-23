// Lean compiler output
// Module: Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.GlobalTheory.HLatOps public import Formalism.HarderNarasimhan.ShiftInvariance public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds public import Formalism.LocalRingCardinality.DataDIVDefs
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
lean_object* lp_mathlib_LinearEquiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_LinearEquiv_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_dualMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___redArg(lean_object* v_inst_1_, lean_object* v_A_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v_addV_5_; lean_object* v_toSemiring_6_; lean_object* v_modV_7_; lean_object* v_toAddMonoid_8_; lean_object* v___x_9_; 
v___x_3_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_4_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_3_);
v_addV_5_ = lean_ctor_get(v_A_2_, 0);
v_toSemiring_6_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toSemiring_6_);
lean_dec_ref(v___x_4_);
v_modV_7_ = lean_ctor_get(v_A_2_, 1);
v_toAddMonoid_8_ = lean_ctor_get(v_addV_5_, 0);
v___x_9_ = lp_mathlib_LinearEquiv_refl(lean_box(0), lean_box(0), v_toSemiring_6_, v_toAddMonoid_8_, v_modV_7_);
lean_dec_ref(v_toSemiring_6_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___redArg___boxed(lean_object* v_inst_10_, lean_object* v_A_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___redArg(v_inst_10_, v_A_11_);
lean_dec_ref(v_A_11_);
lean_dec_ref(v_inst_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_A_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___redArg(v_inst_14_, v_A_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl___boxed(lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_A_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_refl(v_K_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_A_23_);
lean_dec_ref(v_A_23_);
lean_dec(v_inst_22_);
lean_dec_ref(v_inst_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm___redArg(lean_object* v_I_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_mathlib_LinearEquiv_symm___redArg(v_I_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm(lean_object* v_K_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_A_31_, lean_object* v_B_32_, lean_object* v_I_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_mathlib_LinearEquiv_symm___redArg(v_I_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm___boxed(lean_object* v_K_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_A_39_, lean_object* v_B_40_, lean_object* v_I_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_symm(v_K_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_A_39_, v_B_40_, v_I_41_);
lean_dec_ref(v_B_40_);
lean_dec_ref(v_A_39_);
lean_dec(v_inst_38_);
lean_dec_ref(v_inst_36_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans___redArg(lean_object* v_I_43_, lean_object* v_J_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_mathlib_LinearEquiv_trans___redArg(v_I_43_, v_J_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans(lean_object* v_K_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_A_50_, lean_object* v_B_51_, lean_object* v_C_52_, lean_object* v_I_53_, lean_object* v_J_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_mathlib_LinearEquiv_trans___redArg(v_I_53_, v_J_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans___boxed(lean_object* v_K_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_A_60_, lean_object* v_B_61_, lean_object* v_C_62_, lean_object* v_I_63_, lean_object* v_J_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_trans(v_K_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_A_60_, v_B_61_, v_C_62_, v_I_63_, v_J_64_);
lean_dec_ref(v_C_62_);
lean_dec_ref(v_B_61_);
lean_dec_ref(v_A_60_);
lean_dec(v_inst_59_);
lean_dec_ref(v_inst_57_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___redArg(lean_object* v_I_66_){
_start:
{
lean_inc_ref(v_I_66_);
return v_I_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___redArg___boxed(lean_object* v_I_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___redArg(v_I_67_);
lean_dec_ref(v_I_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL(lean_object* v_K_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_A_73_, lean_object* v_B_74_, lean_object* v_I_75_, lean_object* v_L_x27_76_){
_start:
{
lean_inc_ref(v_I_75_);
return v_I_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL___boxed(lean_object* v_K_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_A_81_, lean_object* v_B_82_, lean_object* v_I_83_, lean_object* v_L_x27_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_withL(v_K_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_A_81_, v_B_82_, v_I_83_, v_L_x27_84_);
lean_dec_ref(v_I_83_);
lean_dec_ref(v_B_82_);
lean_dec_ref(v_A_81_);
lean_dec(v_inst_80_);
lean_dec_ref(v_inst_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___redArg(lean_object* v_inst_86_, lean_object* v_A_87_, lean_object* v_B_88_, lean_object* v_I_89_){
_start:
{
lean_object* v___x_90_; lean_object* v_addV_91_; lean_object* v_addV_92_; lean_object* v_toCommSemiring_93_; lean_object* v_modV_94_; lean_object* v_toAddMonoid_95_; lean_object* v_modV_96_; lean_object* v_toAddMonoid_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_90_ = lp_mathlib_Field_toSemifield___redArg(v_inst_86_);
v_addV_91_ = lean_ctor_get(v_B_88_, 0);
lean_inc_ref(v_addV_91_);
v_addV_92_ = lean_ctor_get(v_A_87_, 0);
lean_inc_ref(v_addV_92_);
v_toCommSemiring_93_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_toCommSemiring_93_);
lean_dec_ref(v___x_90_);
v_modV_94_ = lean_ctor_get(v_B_88_, 1);
lean_inc(v_modV_94_);
lean_dec_ref(v_B_88_);
v_toAddMonoid_95_ = lean_ctor_get(v_addV_91_, 0);
lean_inc_ref(v_toAddMonoid_95_);
lean_dec_ref(v_addV_91_);
v_modV_96_ = lean_ctor_get(v_A_87_, 1);
lean_inc(v_modV_96_);
lean_dec_ref(v_A_87_);
v_toAddMonoid_97_ = lean_ctor_get(v_addV_92_, 0);
lean_inc_ref(v_toAddMonoid_97_);
lean_dec_ref(v_addV_92_);
v___x_98_ = lp_mathlib_LinearEquiv_symm___redArg(v_I_89_);
v___x_99_ = lp_mathlib_LinearEquiv_dualMap___redArg(v_toCommSemiring_93_, v_toAddMonoid_95_, v_modV_94_, v_toAddMonoid_97_, v_modV_96_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___redArg___boxed(lean_object* v_inst_100_, lean_object* v_A_101_, lean_object* v_B_102_, lean_object* v_I_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___redArg(v_inst_100_, v_A_101_, v_B_102_, v_I_103_);
lean_dec_ref(v_inst_100_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual(lean_object* v_K_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_A_109_, lean_object* v_B_110_, lean_object* v_inst_111_, lean_object* v_I_112_, lean_object* v_hA_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___redArg(v_inst_106_, v_A_109_, v_B_110_, v_I_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual___boxed(lean_object* v_K_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_A_119_, lean_object* v_B_120_, lean_object* v_inst_121_, lean_object* v_I_122_, lean_object* v_hA_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_Formalism_L2_GlobalTheoryTheory_HLatOps_Iso_dual(v_K_115_, v_inst_116_, v_inst_117_, v_inst_118_, v_A_119_, v_B_120_, v_inst_121_, v_I_122_, v_hA_123_);
lean_dec(v_inst_118_);
lean_dec_ref(v_inst_116_);
return v_res_124_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_HLatOps(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_HLatOpsP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_HLatOps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
