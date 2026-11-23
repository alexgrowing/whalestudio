// Lean compiler output
// Module: Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
// Imports: public import Init public meta import Init public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_convC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_convC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_convC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_convC___redArg(lean_object* v_00_u03b9_1_, lean_object* v_00_u03b6_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_00_u03b9_1_);
lean_ctor_set(v___x_3_, 1, v_00_u03b6_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_convC(lean_object* v_g_4_, lean_object* v_inst_5_, lean_object* v_00_u03b9_6_, lean_object* v_h_u03b9_7_, lean_object* v_00_u03b6_8_, lean_object* v_h_u03b6_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_00_u03b9_6_);
lean_ctor_set(v___x_10_, 1, v_00_u03b6_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_convC___boxed(lean_object* v_g_11_, lean_object* v_inst_12_, lean_object* v_00_u03b9_13_, lean_object* v_h_u03b9_14_, lean_object* v_00_u03b6_15_, lean_object* v_h_u03b6_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_L2_NT_convC(v_g_11_, v_inst_12_, v_00_u03b9_13_, v_h_u03b9_14_, v_00_u03b6_15_, v_h_u03b6_16_);
lean_dec(v_g_11_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
