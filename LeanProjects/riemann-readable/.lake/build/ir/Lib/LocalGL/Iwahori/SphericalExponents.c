// Lean compiler output
// Module: Lib.LocalGL.Iwahori.SphericalExponents
// Imports: public import Init public meta import Init public import Lib.LocalGL.Iwahori.HeckeDegrees
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
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_mk___redArg___lam__0___boxed(lean_object*);
lean_object* lp_GRH_New_intGL_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_inclusion___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Ideal_Quotient_mk___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__0 = (const lean_object*)&lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__0_value;
static const lean_closure_object lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_inclusion___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__1 = (const lean_object*)&lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg(lean_object* v_inst_3_, lean_object* v_N_4_){
_start:
{
lean_object* v_toCommRing_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___f_12_; 
v_toCommRing_5_ = lean_ctor_get(v_inst_3_, 0);
lean_inc_ref(v_toCommRing_5_);
lean_dec_ref(v_inst_3_);
lean_inc(v_N_4_);
v___x_6_ = l_List_finRange(v_N_4_);
v___x_7_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_7_, 0, v_N_4_);
v___x_8_ = lean_box(0);
v___f_9_ = ((lean_object*)(lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__0));
v___x_10_ = lp_GRH_New_intGL_map___redArg(v___x_7_, v___x_6_, v_toCommRing_5_, v___x_8_, v___f_9_);
v___f_11_ = ((lean_object*)(lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg___closed__1));
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_12_, 0, v___f_11_);
lean_closure_set(v___f_12_, 1, v___x_10_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric(lean_object* v_F_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_N_16_, lean_object* v_m_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg(v_inst_14_, v_N_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___boxed(lean_object* v_F_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_N_22_, lean_object* v_m_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric(v_F_19_, v_inst_20_, v_inst_21_, v_N_22_, v_m_23_);
lean_dec(v_m_23_);
lean_dec_ref(v_inst_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol___redArg(lean_object* v_inst_25_, lean_object* v_N_26_, lean_object* v_m_27_, lean_object* v_p_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_19__overap_30_; lean_object* v___x_31_; lean_object* v_val_32_; lean_object* v___x_33_; 
v___x_19__overap_30_ = lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_reduceParahoric___redArg(v_inst_25_, v_N_26_);
v___x_31_ = lean_apply_1(v___x_19__overap_30_, v_p_28_);
v_val_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_val_32_);
lean_dec_ref(v___x_31_);
v___x_33_ = lp_mathlib_Matrix_transpose___redArg(v_val_32_, v_m_27_, v_a_29_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol(lean_object* v_F_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_N_37_, lean_object* v_m_38_, lean_object* v_p_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol___redArg(v_inst_35_, v_N_37_, v_m_38_, v_p_39_, v_a_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol___boxed(lean_object* v_F_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_N_45_, lean_object* v_m_46_, lean_object* v_p_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH___private_Lib_LocalGL_Iwahori_SphericalExponents_0__New_residueCol(v_F_42_, v_inst_43_, v_inst_44_, v_N_45_, v_m_46_, v_p_47_, v_a_48_);
lean_dec_ref(v_inst_44_);
return v_res_49_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Iwahori_HeckeDegrees(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_LocalGL_Iwahori_SphericalExponents(uint8_t builtin) {
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
res = initialize_GRH_Lib_LocalGL_Iwahori_HeckeDegrees(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
