// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EqOfPowEqOne
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq___redArg(lean_object* v_a_1_){
_start:
{
lean_inc(v_a_1_);
return v_a_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq___redArg___boxed(lean_object* v_a_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_HC_D7_sqq___redArg(v_a_2_);
lean_dec(v_a_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq(lean_object* v_00_u03c6_4_, lean_object* v_hinj_5_, lean_object* v_q_6_, lean_object* v_d_7_, lean_object* v_hH_8_, lean_object* v_he_9_, lean_object* v_L_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_00_u03b6_13_, lean_object* v_a_14_, lean_object* v_b_15_, lean_object* v_h_16_){
_start:
{
lean_inc(v_a_14_);
return v_a_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_D7_sqq___boxed(lean_object* v_00_u03c6_17_, lean_object* v_hinj_18_, lean_object* v_q_19_, lean_object* v_d_20_, lean_object* v_hH_21_, lean_object* v_he_22_, lean_object* v_L_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_00_u03b6_26_, lean_object* v_a_27_, lean_object* v_b_28_, lean_object* v_h_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_HC_D7_sqq(v_00_u03c6_17_, v_hinj_18_, v_q_19_, v_d_20_, v_hH_21_, v_he_22_, v_L_23_, v_inst_24_, v_inst_25_, v_00_u03b6_26_, v_a_27_, v_b_28_, v_h_29_);
lean_dec(v_b_28_);
lean_dec(v_a_27_);
lean_dec(v_00_u03b6_26_);
lean_dec_ref(v_inst_24_);
lean_dec(v_d_20_);
lean_dec(v_q_19_);
lean_dec_ref(v_00_u03c6_17_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EqOfPowEqOne(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_NonemptyFieldAxiomsCyclicPow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EqOfPowEqOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
