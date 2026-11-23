// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.RowSideTie
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.LiftLat public import Formalism.LocalRingCardinality.PrincipalHermitianLattice public import Formalism.LocalRingCardinality.DataIdx public import Formalism.LocalToGlobal.Divisibility.DefGroup
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symPos(lean_object* v_r_1_, lean_object* v_00_u03c1_2_, lean_object* v_k_3_, lean_object* v_i_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_i_4_, v_00_u03c1_2_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_nat_add(v_00_u03c1_2_, v_k_3_);
v___x_7_ = lean_nat_dec_lt(v_i_4_, v___x_6_);
lean_dec(v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_nat_mod(v_i_4_, v_r_1_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_nat_sub(v_i_4_, v_00_u03c1_2_);
v___x_10_ = lean_nat_mod(v___x_9_, v_r_1_);
lean_dec(v___x_9_);
return v___x_10_;
}
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_nat_add(v_k_3_, v_i_4_);
v___x_12_ = lean_nat_mod(v___x_11_, v_r_1_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symPos___boxed(lean_object* v_r_13_, lean_object* v_00_u03c1_14_, lean_object* v_k_15_, lean_object* v_i_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_L2_DIV_symPos(v_r_13_, v_00_u03c1_14_, v_k_15_, v_i_16_);
lean_dec(v_i_16_);
lean_dec(v_k_15_);
lean_dec(v_00_u03c1_14_);
lean_dec(v_r_13_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataIdx(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_RowSideTie(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
