// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.ThShort
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_stdLat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_stdLat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_GenLat_Ln(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_GenLat_Ln___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Mfr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Mfr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_stdLat(lean_object* v_E_1_, lean_object* v_inst_2_, lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_stdLat___boxed(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_L2_Pj_stdLat(v_E_5_, v_inst_6_, v_n_7_);
lean_dec(v_n_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_GenLat_Ln(lean_object* v_E_9_, lean_object* v_inst_10_, lean_object* v_n_11_, lean_object* v_00_u039b_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_GenLat_Ln___boxed(lean_object* v_E_14_, lean_object* v_inst_15_, lean_object* v_n_16_, lean_object* v_00_u039b_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Pj_GenLat_Ln(v_E_14_, v_inst_15_, v_n_16_, v_00_u039b_17_);
lean_dec(v_n_16_);
lean_dec_ref(v_inst_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Mfr(lean_object* v_E_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_H_23_, lean_object* v_l_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Mfr___boxed(lean_object* v_E_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_H_30_, lean_object* v_l_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_L2_Pj_Mfr(v_E_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_H_30_, v_l_31_);
lean_dec_ref(v_l_31_);
lean_dec_ref(v_H_30_);
lean_dec_ref(v_inst_27_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThProps(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThShort(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThProps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
