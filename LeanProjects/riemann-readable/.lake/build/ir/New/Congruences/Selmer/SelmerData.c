// Lean compiler output
// Module: New.Congruences.Selmer.SelmerData
// Imports: public import Init public meta import Init public import Lib.ClassField.GaloisCohomology.TameSelmerCocycles public import Lib.ClassField.GreenbergWiles.SelmerLevels public import Lib.General.NumberTheory.CoefficientRings public import New.Congruences.Selmer.AuxiliaryPrimes
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
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Selmer_conjDualHom___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom(lean_object* v_00_u2113_5_, lean_object* v_inst_6_, lean_object* v_E_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_O_11_, lean_object* v_n_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_00_u03c1_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_conjDualHom___boxed(lean_object* v_00_u2113_20_, lean_object* v_inst_21_, lean_object* v_E_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_O_26_, lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_00_u03c1_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_Selmer_conjDualHom(v_00_u2113_20_, v_inst_21_, v_E_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_O_26_, v_n_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_00_u03c1_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec(v_00_u03c1_32_);
lean_dec_ref(v_inst_31_);
lean_dec(v_inst_30_);
lean_dec_ref(v_inst_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec(v_00_u2113_20_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GaloisCohomology_TameSelmerCocycles(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_SelmerLevels(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_CoefficientRings(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Selmer_SelmerData(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_GaloisCohomology_TameSelmerCocycles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_GreenbergWiles_SelmerLevels(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_CoefficientRings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
