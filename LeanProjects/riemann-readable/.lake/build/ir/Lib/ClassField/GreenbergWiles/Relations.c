// Lean compiler output
// Module: Lib.ClassField.GreenbergWiles.Relations
// Imports: public import Init public meta import Init public import Lib.ClassField.GreenbergWiles.CocycleCounts public import Lib.ClassField.GreenbergWiles.SelmerRelations
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
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_RelationSetting_relations___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations(lean_object* v_K_5_, lean_object* v_R_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_M_10_, lean_object* v_m_11_, lean_object* v_inst_12_, lean_object* v_D_13_, lean_object* v_T_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_relations___boxed(lean_object* v_K_16_, lean_object* v_R_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_M_21_, lean_object* v_m_22_, lean_object* v_inst_23_, lean_object* v_D_24_, lean_object* v_T_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_RelationSetting_relations(v_K_16_, v_R_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_M_21_, v_m_22_, v_inst_23_, v_D_24_, v_T_25_);
lean_dec(v_T_25_);
lean_dec_ref(v_D_24_);
lean_dec(v_m_22_);
lean_dec_ref(v_M_21_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_CocycleCounts(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_SelmerRelations(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_Relations(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_GreenbergWiles_CocycleCounts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_GreenbergWiles_SelmerRelations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
