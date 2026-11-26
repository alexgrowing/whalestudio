// Lean compiler output
// Module: Lib.ClassField.GreenbergWiles.SelmerLevels
// Imports: public import Init public meta import Init public import Lib.ClassField.Global.ExistenceTheorem
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
lean_object* lp_mathlib_Quotient_map_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_x1_2_, lean_object* v_x2_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_x1_2_, v_x2_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___redArg(lean_object* v_inst_5_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___f_6_ = lean_alloc_closure((void*)(lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6_, 0, v_inst_5_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_closure((void*)(lp_mathlib_Quotient_map_u2082), 10, 8);
lean_closure_set(v___x_8_, 0, lean_box(0));
lean_closure_set(v___x_8_, 1, lean_box(0));
lean_closure_set(v___x_8_, 2, v___x_7_);
lean_closure_set(v___x_8_, 3, v___x_7_);
lean_closure_set(v___x_8_, 4, lean_box(0));
lean_closure_set(v___x_8_, 5, v___x_7_);
lean_closure_set(v___x_8_, 6, v___f_6_);
lean_closure_set(v___x_8_, 7, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib(lean_object* v_G_9_, lean_object* v_X_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_Q_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___redArg(v_inst_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib___boxed(lean_object* v_G_16_, lean_object* v_X_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_Q_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_instMulActionQuotientSubgroupQuotientSubtypeMem__lib(v_G_16_, v_X_17_, v_inst_18_, v_inst_19_, v_Q_20_, v_inst_21_);
lean_dec_ref(v_inst_18_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Global_ExistenceTheorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_SelmerLevels(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Global_ExistenceTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
