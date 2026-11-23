// Lean compiler output
// Module: Formalism.SatakeDualWeyl.NablaRepApply
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LinSubstIsHomogeneous public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
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
lean_object* lp_tree_Formalism_UG_stdAct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_UG_tensAct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdRep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_tensRep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_tensRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdRep___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_stdAct___boxed), 6, 5);
lean_closure_set(v___x_4_, 0, lean_box(0));
lean_closure_set(v___x_4_, 1, v_inst_1_);
lean_closure_set(v___x_4_, 2, lean_box(0));
lean_closure_set(v___x_4_, 3, v_inst_2_);
lean_closure_set(v___x_4_, 4, v_inst_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdRep(lean_object* v_O_5_, lean_object* v_inst_6_, lean_object* v_n_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_stdAct___boxed), 6, 5);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, v_inst_6_);
lean_closure_set(v___x_10_, 2, lean_box(0));
lean_closure_set(v___x_10_, 3, v_inst_8_);
lean_closure_set(v___x_10_, 4, v_inst_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_tensRep___redArg(lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_tensAct___boxed), 7, 6);
lean_closure_set(v___x_15_, 0, lean_box(0));
lean_closure_set(v___x_15_, 1, v_inst_11_);
lean_closure_set(v___x_15_, 2, lean_box(0));
lean_closure_set(v___x_15_, 3, v_inst_12_);
lean_closure_set(v___x_15_, 4, v_inst_13_);
lean_closure_set(v___x_15_, 5, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_tensRep(lean_object* v_O_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_tensAct___boxed), 7, 6);
lean_closure_set(v___x_22_, 0, lean_box(0));
lean_closure_set(v___x_22_, 1, v_inst_17_);
lean_closure_set(v___x_22_, 2, lean_box(0));
lean_closure_set(v___x_22_, 3, v_inst_19_);
lean_closure_set(v___x_22_, 4, v_inst_20_);
lean_closure_set(v___x_22_, 5, v_k_21_);
return v___x_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_NablaRepApply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
