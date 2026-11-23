// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_TensorProduct_AlgebraTensorModule_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg(lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_f_7_){
_start:
{
lean_object* v___x_8_; lean_object* v_toSemiring_9_; lean_object* v_toCommSemiring_10_; lean_object* v_toAddCommMonoid_11_; lean_object* v_toSMul_12_; lean_object* v_toAddMonoid_13_; lean_object* v___f_14_; lean_object* v___x_15_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_2_);
v_toSemiring_9_ = lean_ctor_get(v_inst_3_, 0);
lean_inc_ref(v_toSemiring_9_);
lean_dec_ref(v_inst_3_);
v_toCommSemiring_10_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_toCommSemiring_10_);
lean_dec_ref(v___x_8_);
v_toAddCommMonoid_11_ = lean_ctor_get(v_toSemiring_9_, 0);
lean_inc_ref_n(v_toAddCommMonoid_11_, 2);
lean_dec_ref(v_toSemiring_9_);
v_toSMul_12_ = lean_ctor_get(v_inst_4_, 0);
lean_inc_n(v_toSMul_12_, 2);
lean_dec_ref(v_inst_4_);
v_toAddMonoid_13_ = lean_ctor_get(v_inst_5_, 0);
lean_inc_ref(v_toAddMonoid_13_);
lean_dec_ref(v_inst_5_);
v___f_14_ = ((lean_object*)(lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg___closed__0));
v___x_15_ = lp_mathlib_TensorProduct_AlgebraTensorModule_map___redArg(v_toCommSemiring_10_, v_toAddCommMonoid_11_, v_toSMul_12_, v_toAddMonoid_13_, v_inst_6_, v_toAddCommMonoid_11_, v_toSMul_12_, v_f_7_, v___f_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg___boxed(lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_f_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg(v_inst_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_f_21_);
lean_dec_ref(v_inst_16_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap(lean_object* v_Qp_23_, lean_object* v_inst_24_, lean_object* v_B_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_LL_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_V_31_, lean_object* v_V_x27_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_f_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___redArg(v_inst_24_, v_inst_26_, v_inst_27_, v_inst_37_, v_inst_39_, v_f_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap___boxed(lean_object** _args){
lean_object* v_Qp_43_ = _args[0];
lean_object* v_inst_44_ = _args[1];
lean_object* v_B_45_ = _args[2];
lean_object* v_inst_46_ = _args[3];
lean_object* v_inst_47_ = _args[4];
lean_object* v_LL_48_ = _args[5];
lean_object* v_inst_49_ = _args[6];
lean_object* v_inst_50_ = _args[7];
lean_object* v_V_51_ = _args[8];
lean_object* v_V_x27_52_ = _args[9];
lean_object* v_inst_53_ = _args[10];
lean_object* v_inst_54_ = _args[11];
lean_object* v_inst_55_ = _args[12];
lean_object* v_inst_56_ = _args[13];
lean_object* v_inst_57_ = _args[14];
lean_object* v_inst_58_ = _args[15];
lean_object* v_inst_59_ = _args[16];
lean_object* v_inst_60_ = _args[17];
lean_object* v_f_61_ = _args[18];
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_MainNotions_TruncatedSeriesCountingBounds_crisMap(v_Qp_43_, v_inst_44_, v_B_45_, v_inst_46_, v_inst_47_, v_LL_48_, v_inst_49_, v_inst_50_, v_V_51_, v_V_x27_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_f_61_);
lean_dec(v_inst_58_);
lean_dec(v_inst_55_);
lean_dec(v_inst_54_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_50_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_44_);
return v_res_62_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_LiftingTheory(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DeltaInvariantLattices(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_CrystallineMapLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_LiftingTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DeltaInvariantLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
