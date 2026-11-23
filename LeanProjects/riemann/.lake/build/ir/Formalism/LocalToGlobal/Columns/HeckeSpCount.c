// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.HeckeSpCount
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.HeckeSp public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre___lam__1(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_hcntFibre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_hcntFibre___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_hcntFibre___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_hcntFibre___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Col_hcntFibre___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_hcntFibre___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_hcntFibre___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Col_hcntFibre___closed__1_value;
static const lean_ctor_object lp_tree_Formalism_L2_Col_hcntFibre___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Col_hcntFibre___closed__0_value),((lean_object*)&lp_tree_Formalism_L2_Col_hcntFibre___closed__1_value)}};
static const lean_object* lp_tree_Formalism_L2_Col_hcntFibre___closed__2 = (const lean_object*)&lp_tree_Formalism_L2_Col_hcntFibre___closed__2_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre___lam__0(lean_object* v_s_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_s_1_, v___y_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre___lam__1(lean_object* v_t_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_1(v_t_4_, v___y_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre(lean_object* v_K_12_, lean_object* v_V_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_i_18_, lean_object* v_U_19_, lean_object* v_hU_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = ((lean_object*)(lp_tree_Formalism_L2_Col_hcntFibre___closed__2));
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hcntFibre___boxed(lean_object* v_K_22_, lean_object* v_V_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_i_28_, lean_object* v_U_29_, lean_object* v_hU_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_Col_hcntFibre(v_K_22_, v_V_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_i_28_, v_U_29_, v_hU_30_);
lean_dec(v_i_28_);
lean_dec(v_inst_26_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSpCount(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
