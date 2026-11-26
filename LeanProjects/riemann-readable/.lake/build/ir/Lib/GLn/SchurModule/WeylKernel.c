// Lean compiler output
// Module: Lib.GLn.SchurModule.WeylKernel
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.Defs public import Lib.GLn.SchurModule.TensorModel public import Lib.Shimura.ComplexTheta.AppellHumbertData
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
lean_object* lp_mathlib_Equiv_refl___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_GL_squarePart___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GL_squarePart___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart___redArg___lam__0(lean_object* v_00_u03c4_1_, lean_object* v_e_2_, lean_object* v_y_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toFun_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_17_; 
lean_inc(v_00_u03c4_1_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_00_u03c4_1_);
lean_ctor_set(v___x_6_, 1, v_a_4_);
v___x_7_ = lean_apply_1(v_e_2_, v_00_u03c4_1_);
v_toFun_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_17_ == 0)
{
lean_object* v_unused_18_; 
v_unused_18_ = lean_ctor_get(v___x_7_, 1);
lean_dec(v_unused_18_);
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_toFun_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_12_ = lean_apply_1(v_toFun_8_, v_b_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_12_);
lean_ctor_set(v___x_10_, 0, v___x_6_);
v___x_14_ = v___x_10_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_6_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_12_);
v___x_14_ = v_reuseFailAlloc_16_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
lean_object* v___x_15_; 
v___x_15_ = lean_apply_1(v_y_3_, v___x_14_);
return v___x_15_;
}
}
}
}
static lean_object* _init_lp_GRH_New_GL_squarePart___redArg___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_mathlib_Equiv_refl___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart___redArg(lean_object* v_e_20_, lean_object* v_y_21_, lean_object* v_00_u03c4_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; lean_object* v_toFun_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v___x_25_ = lean_obj_once(&lp_GRH_New_GL_squarePart___redArg___closed__0, &lp_GRH_New_GL_squarePart___redArg___closed__0_once, _init_lp_GRH_New_GL_squarePart___redArg___closed__0);
v_toFun_26_ = lean_ctor_get(v___x_25_, 0);
v___f_27_ = lean_alloc_closure((void*)(lp_GRH_New_GL_squarePart___redArg___lam__0), 5, 3);
lean_closure_set(v___f_27_, 0, v_00_u03c4_22_);
lean_closure_set(v___f_27_, 1, v_e_20_);
lean_closure_set(v___f_27_, 2, v_y_21_);
lean_inc(v_toFun_26_);
v___x_28_ = lean_apply_3(v_toFun_26_, v___f_27_, v_a_23_, v_a_24_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart(lean_object* v_00_u03a6_29_, lean_object* v_R_30_, lean_object* v_n_31_, lean_object* v_inst_32_, lean_object* v_e_33_, lean_object* v_y_34_, lean_object* v_00_u03c4_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_GRH_New_GL_squarePart___redArg(v_e_33_, v_y_34_, v_00_u03c4_35_, v_a_36_, v_a_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_squarePart___boxed(lean_object* v_00_u03a6_39_, lean_object* v_R_40_, lean_object* v_n_41_, lean_object* v_inst_42_, lean_object* v_e_43_, lean_object* v_y_44_, lean_object* v_00_u03c4_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_GL_squarePart(v_00_u03a6_39_, v_R_40_, v_n_41_, v_inst_42_, v_e_43_, v_y_44_, v_00_u03c4_45_, v_a_46_, v_a_47_);
lean_dec(v_inst_42_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_TensorModel(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ComplexTheta_AppellHumbertData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GLn_SchurModule_WeylKernel(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_SchurModule_TensorModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ComplexTheta_AppellHumbertData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
