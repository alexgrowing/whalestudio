// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianColumns.TiedQCJoint
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm public import Formalism.LocalToGlobal.HermitianColumns.TiedQC
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
lean_object* lp_mathlib_Equiv_cast(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Herm_clsCast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Herm_clsCast___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_clsCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_clsCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_yCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_yCast___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Herm_clsCast___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_cast(lean_box(0), lean_box(0), lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_clsCast(lean_object* v_D_2_, lean_object* v_u_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_L2_Herm_clsCast___closed__0, &lp_tree_Formalism_L2_Herm_clsCast___closed__0_once, _init_lp_tree_Formalism_L2_Herm_clsCast___closed__0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_clsCast___boxed(lean_object* v_D_6_, lean_object* v_u_7_, lean_object* v_i_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_L2_Herm_clsCast(v_D_6_, v_u_7_, v_i_8_);
lean_dec(v_i_8_);
lean_dec(v_u_7_);
lean_dec_ref(v_D_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_yCast(lean_object* v_D_10_, lean_object* v_u_11_, lean_object* v_i_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&lp_tree_Formalism_L2_Herm_clsCast___closed__0, &lp_tree_Formalism_L2_Herm_clsCast___closed__0_once, _init_lp_tree_Formalism_L2_Herm_clsCast___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Herm_yCast___boxed(lean_object* v_D_14_, lean_object* v_u_15_, lean_object* v_i_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_L2_Herm_yCast(v_D_14_, v_u_15_, v_i_16_);
lean_dec(v_i_16_);
lean_dec(v_u_15_);
lean_dec_ref(v_D_14_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ColsHerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_TiedQC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_TiedQCJoint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_ColsHerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_TiedQC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
