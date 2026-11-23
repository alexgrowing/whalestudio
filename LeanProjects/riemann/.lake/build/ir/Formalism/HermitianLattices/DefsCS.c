// Lean compiler output
// Module: Formalism.HermitianLattices.DefsCS
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.StatementLat
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
lean_object* lp_mathlib_AddSubgroup_toIntSubmodule___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_toEmbedding___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_zmap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_zmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_zmap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_zmap___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lp_mathlib_AddSubgroup_toIntSubmodule___redArg(v_inst_1_);
v___x_3_ = lean_box(0);
v___x_4_ = lp_mathlib_Equiv_toEmbedding___redArg___lam__0(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_zmap(lean_object* v_V_5_, lean_object* v_W_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_R_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_00_u03b9_12_, lean_object* v_M_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_HermitianLatticesTheory_zmap___redArg(v_inst_8_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_zmap___boxed(lean_object* v_V_15_, lean_object* v_W_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_R_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_00_u03b9_22_, lean_object* v_M_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_HermitianLatticesTheory_zmap(v_V_15_, v_W_16_, v_inst_17_, v_inst_18_, v_R_19_, v_inst_20_, v_inst_21_, v_00_u03b9_22_, v_M_23_);
lean_dec(v_00_u03b9_22_);
lean_dec(v_inst_21_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_17_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HermitianLattices_DefsCS(uint8_t builtin) {
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
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
