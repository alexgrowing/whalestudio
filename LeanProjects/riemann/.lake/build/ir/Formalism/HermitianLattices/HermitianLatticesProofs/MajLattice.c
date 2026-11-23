// Lean compiler output
// Module: Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.StatementMaj public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonMajorizingLattice public import Lemmata.GeneralBFactSecondRest.Imports
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_majLattice__u___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_majLattice__u(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_majLattice__u___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_majLattice__u___redArg(lean_object* v_z_1_, lean_object* v_v_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_snd_5_; lean_object* v___x_6_; 
v___x_4_ = lean_apply_1(v_z_1_, v_i_3_);
v_snd_5_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_apply_1(v_snd_5_, v_v_2_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_majLattice__u(lean_object* v_K_7_, lean_object* v_00_u03b9_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_z_11_, lean_object* v_v_12_, lean_object* v_i_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_HermitianLatticesTheory_majLattice__u___redArg(v_z_11_, v_v_12_, v_i_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_majLattice__u___boxed(lean_object* v_K_15_, lean_object* v_00_u03b9_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_z_19_, lean_object* v_v_20_, lean_object* v_i_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_HermitianLatticesTheory_majLattice__u(v_K_15_, v_00_u03b9_16_, v_inst_17_, v_inst_18_, v_z_19_, v_v_20_, v_i_21_);
lean_dec_ref(v_inst_17_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementMaj(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice(uint8_t builtin);
lean_object* initialize_tree_Lemmata_GeneralBFactSecondRest_Imports(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice(uint8_t builtin) {
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
res = initialize_tree_Formalism_HermitianLattices_StatementMaj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_GeneralBFactSecondRest_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
