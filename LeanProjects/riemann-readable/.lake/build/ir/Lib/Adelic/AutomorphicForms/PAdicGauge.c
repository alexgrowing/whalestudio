// Lean compiler output
// Module: Lib.Adelic.AutomorphicForms.PAdicGauge
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.HeckeEigenforms public import Lib.General.LinearAlgebra.MatrixNormBounds public import Lib.PadicComparison.Descent.TestCategory
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
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_placeAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_placeAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_placeAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___closed__0 = (const lean_object*)&lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_placeAt___redArg(lean_object* v_P_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_chosenPlace_3_; lean_object* v_twistPlace_4_; lean_object* v___x_5_; 
v_chosenPlace_3_ = lean_ctor_get(v_P_1_, 2);
lean_inc_ref(v_chosenPlace_3_);
v_twistPlace_4_ = lean_ctor_get(v_P_1_, 3);
lean_inc_ref(v_twistPlace_4_);
lean_dec_ref(v_P_1_);
v___x_5_ = l_Sum_elim___redArg(v_chosenPlace_3_, v_twistPlace_4_, v_a_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_placeAt(lean_object* v_E_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_P_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_chosenPlace_12_; lean_object* v_twistPlace_13_; lean_object* v___x_14_; 
v_chosenPlace_12_ = lean_ctor_get(v_P_10_, 2);
lean_inc_ref(v_chosenPlace_12_);
v_twistPlace_13_ = lean_ctor_get(v_P_10_, 3);
lean_inc_ref(v_twistPlace_13_);
lean_dec_ref(v_P_10_);
v___x_14_ = l_Sum_elim___redArg(v_chosenPlace_12_, v_twistPlace_13_, v_a_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_placeAt___boxed(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_P_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_GRH_New_LevelPlaces_placeAt(v_E_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_P_19_, v_a_20_);
lean_dec_ref(v_inst_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___lam__0(lean_object* v_x_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_apply_2(v_x_22_, v___y_23_, v___y_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg(){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = ((lean_object*)(lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___closed__0));
return v___f_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___boxed(lean_object* v___dummy_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg();
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex(lean_object* v_E_31_, lean_object* v_n_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_S_37_, lean_object* v_H_38_, lean_object* v_00_u03c7_39_, lean_object* v_00_u03ba_40_, lean_object* v_e_41_){
_start:
{
lean_object* v___f_42_; 
v___f_42_ = ((lean_object*)(lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___redArg___closed__0));
return v___f_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex___boxed(lean_object* v_E_43_, lean_object* v_n_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_S_49_, lean_object* v_H_50_, lean_object* v_00_u03c7_51_, lean_object* v_00_u03ba_52_, lean_object* v_e_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_GRH_New_LevelPlaces_instCoeFunLevelFormForallGfForallWeylIndexInfinitePlaceComplex(v_E_43_, v_n_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_S_49_, v_H_50_, v_00_u03c7_51_, v_00_u03ba_52_, v_e_53_);
lean_dec_ref(v_e_53_);
lean_dec_ref(v_00_u03ba_52_);
lean_dec_ref(v_00_u03c7_51_);
lean_dec_ref(v_S_49_);
lean_dec_ref(v_inst_48_);
lean_dec(v_inst_47_);
lean_dec_ref(v_inst_46_);
lean_dec_ref(v_inst_45_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm___redArg___lam__0(lean_object* v_g_55_, lean_object* v_00_u03c6_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_2(v_00_u03c6_56_, v_g_55_, v___y_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm___redArg(lean_object* v_g_59_){
_start:
{
lean_object* v___f_60_; 
v___f_60_ = lean_alloc_closure((void*)(lp_GRH_New_Rows_evalForm___redArg___lam__0), 3, 1);
lean_closure_set(v___f_60_, 0, v_g_59_);
return v___f_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm(lean_object* v_E_61_, lean_object* v_n_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_S_67_, lean_object* v_H_68_, lean_object* v_00_u03c7_69_, lean_object* v_00_u03ba_70_, lean_object* v_e_71_, lean_object* v_g_72_){
_start:
{
lean_object* v___f_73_; 
v___f_73_ = lean_alloc_closure((void*)(lp_GRH_New_Rows_evalForm___redArg___lam__0), 3, 1);
lean_closure_set(v___f_73_, 0, v_g_72_);
return v___f_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_evalForm___boxed(lean_object* v_E_74_, lean_object* v_n_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_S_80_, lean_object* v_H_81_, lean_object* v_00_u03c7_82_, lean_object* v_00_u03ba_83_, lean_object* v_e_84_, lean_object* v_g_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_Rows_evalForm(v_E_74_, v_n_75_, v_inst_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_S_80_, v_H_81_, v_00_u03c7_82_, v_00_u03ba_83_, v_e_84_, v_g_85_);
lean_dec_ref(v_e_84_);
lean_dec_ref(v_00_u03ba_83_);
lean_dec_ref(v_00_u03c7_82_);
lean_dec_ref(v_S_80_);
lean_dec_ref(v_inst_79_);
lean_dec(v_inst_78_);
lean_dec_ref(v_inst_77_);
lean_dec_ref(v_inst_76_);
return v_res_86_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_HeckeEigenforms(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_Descent_TestCategory(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_PAdicGauge(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_HeckeEigenforms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_Descent_TestCategory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
