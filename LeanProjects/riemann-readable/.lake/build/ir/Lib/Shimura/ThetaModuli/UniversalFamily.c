// Lean compiler output
// Module: Lib.Shimura.ThetaModuli.UniversalFamily
// Imports: public import Init public meta import Init public import Lib.General.Geometry.SmoothnessCriterion public import Lib.Shimura.Deformation.TangentBound public import Lib.Shimura.GoodReduction.MultiplicativeNorm public import Lib.Shimura.IntegralModel.BallImmersion public import Lib.Shimura.ThetaModuli.FamilyFromPoints
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v_torus_4_; lean_object* v___x_5_; 
v_fst_2_ = lean_ctor_get(v_a_1_, 0);
lean_inc(v_fst_2_);
v_snd_3_ = lean_ctor_get(v_a_1_, 1);
lean_inc(v_snd_3_);
lean_dec_ref(v_a_1_);
v_torus_4_ = lean_ctor_get(v_fst_2_, 3);
lean_inc_ref(v_torus_4_);
lean_dec(v_fst_2_);
v___x_5_ = lean_apply_1(v_torus_4_, v_snd_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus(lean_object* v_E_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_D_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_fst_11_; lean_object* v_snd_12_; lean_object* v_torus_13_; lean_object* v___x_14_; 
v_fst_11_ = lean_ctor_get(v_a_10_, 0);
lean_inc(v_fst_11_);
v_snd_12_ = lean_ctor_get(v_a_10_, 1);
lean_inc(v_snd_12_);
lean_dec_ref(v_a_10_);
v_torus_13_ = lean_ctor_get(v_fst_11_, 3);
lean_inc_ref(v_torus_13_);
lean_dec(v_fst_11_);
v___x_14_ = lean_apply_1(v_torus_13_, v_snd_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus___boxed(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_D_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_Variety_ThetaNull_FamilyParameter_torus(v_E_15_, v_inst_16_, v_inst_17_, v_D_18_, v_a_19_);
lean_dec_ref(v_D_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Geometry_SmoothnessCriterion(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Deformation_TangentBound(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_GoodReduction_MultiplicativeNorm(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_IntegralModel_BallImmersion(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_FamilyFromPoints(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_UniversalFamily(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Geometry_SmoothnessCriterion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Deformation_TangentBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_GoodReduction_MultiplicativeNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_IntegralModel_BallImmersion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaModuli_FamilyFromPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
