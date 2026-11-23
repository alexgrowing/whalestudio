// Lean compiler output
// Module: Formalism.LatticeTheta.LatticeThetaProofs.TorusProjIsOpenQuotientMap
// Imports: public import Init public meta import Init public import Formalism.LatticeTheta.LatticeThetaProofs.InnerDualVecBasis public import Formalism.LatticeTheta.LatticeThetaProofs.FundamentalDomainEqPreimage
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
LEAN_EXPORT lean_object* lp_tree_Formalism_H_torusProj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_H_torusProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_H_torusProj___redArg(lean_object* v_t_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_t_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_H_torusProj(lean_object* v_00_u03b9_4_, lean_object* v_t_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_apply_1(v_t_5_, v_i_6_);
return v___x_7_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
