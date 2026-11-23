// Lean compiler output
// Module: ReciprocityTheory.GaloisValuations.GlobalB
// Imports: public import Init public meta import Init public import ReciprocityTheory.GaloisValuations.GlobalA
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
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_IntCl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_IntCl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_primeBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_primeBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_IntCl(lean_object* v_F_1_, lean_object* v_00_u03a9_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_IntCl___boxed(lean_object* v_F_7_, lean_object* v_00_u03a9_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_ReciprocityTheory_Gal_IntCl(v_F_7_, v_00_u03a9_8_, v_inst_9_, v_inst_10_, v_inst_11_);
lean_dec_ref(v_inst_11_);
lean_dec_ref(v_inst_10_);
lean_dec_ref(v_inst_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_primeBelow(lean_object* v_F_13_, lean_object* v_00_u03a9_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_A_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_primeBelow___boxed(lean_object* v_F_22_, lean_object* v_00_u03a9_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_A_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_ReciprocityTheory_Gal_primeBelow(v_F_22_, v_00_u03a9_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_A_29_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_24_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_GaloisValuations_GlobalA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_GaloisValuations_GlobalB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_GaloisValuations_GlobalA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
