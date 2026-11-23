// Lean compiler output
// Module: ReciprocityTheory.Hypotheses.GalCoh
// Imports: public import Init public meta import Init public import ReciprocityTheory.Hypotheses.GalCohDefs
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
lean_object* lp_tree_ReciprocityTheory_Gal_locHom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_tree_ReciprocityTheory_Gal_locHom___redArg(v_inst_1_, v_inst_2_, v_inst_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam___redArg___boxed(lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_ReciprocityTheory_Gal_locFam___redArg(v_inst_5_, v_inst_6_, v_inst_7_);
lean_dec_ref(v_inst_6_);
lean_dec_ref(v_inst_5_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam(lean_object* v_F_9_, lean_object* v_00_u03a9_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_S_14_, lean_object* v_Av_15_, lean_object* v_v_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_ReciprocityTheory_Gal_locHom___redArg(v_inst_11_, v_inst_12_, v_inst_13_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_Gal_locFam___boxed(lean_object* v_F_18_, lean_object* v_00_u03a9_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_S_23_, lean_object* v_Av_24_, lean_object* v_v_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_ReciprocityTheory_Gal_locFam(v_F_18_, v_00_u03a9_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_S_23_, v_Av_24_, v_v_25_);
lean_dec_ref(v_Av_24_);
lean_dec(v_S_23_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_Hypotheses_GalCohDefs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_Hypotheses_GalCoh(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_Hypotheses_GalCohDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
