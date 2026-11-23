// Lean compiler output
// Module: Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLabWD public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
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
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_msOf_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_msOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_msOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_msOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_msOf_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_16_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_16_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_16_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_16_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_a_9_; lean_object* v_d_10_; lean_object* v___x_11_; lean_object* v___x_13_; 
v_a_9_ = lean_ctor_get(v_head_4_, 0);
lean_inc(v_a_9_);
v_d_10_ = lean_ctor_get(v_head_4_, 2);
lean_inc(v_d_10_);
lean_dec(v_head_4_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_a_9_);
lean_ctor_set(v___x_11_, 1, v_d_10_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v___x_11_);
v___x_13_ = v___x_7_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_11_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v_a_2_);
v___x_13_ = v_reuseFailAlloc_15_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_13_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_msOf___redArg(lean_object* v_Sig_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_box(0);
v___x_19_ = lp_tree_List_mapTR_loop___at___00Formalism_L2_msOf_spec__0(v_Sig_17_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_msOf(lean_object* v_D_20_, lean_object* v_Sig_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_tree_Formalism_L2_msOf___redArg(v_Sig_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_msOf___boxed(lean_object* v_D_23_, lean_object* v_Sig_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_L2_msOf(v_D_23_, v_Sig_24_);
lean_dec_ref(v_D_23_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_JointConditionsZpowers_IrreducibilityOfTheoremThree(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLabWD(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_GlobalDatumRegularityOfTypesCompatibility(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_JointConditionsZpowers_IrreducibilityOfTheoremThree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLabWD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
