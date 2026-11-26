// Lean compiler output
// Module: Lib.DiscreteSeries.Character.FormalDegree
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Character.MultiplicityOrbitalIntegral public import Lib.DiscreteSeries.Character.OpenOrbitIntegral
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
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_GRH_New_HCParam_compactForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_paramAddRho___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_HCParam_lowerCount___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Orbital_numeratorExponent___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__0;
static lean_once_cell_t lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Orbital_numeratorExponent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Orbital_numeratorExponent___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Orbital_numeratorExponent___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Orbital_numeratorExponent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Orbital_numeratorExponent___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__0(lean_object* v_l_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_apply_1(v_l_1_, v___y_2_);
v___x_4_ = lean_int_neg(v___x_3_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Orbital_numeratorExponent___redArg___lam__1(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_8_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_7_, v_a_5_, v_b_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__1___boxed(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_GRH_New_Orbital_numeratorExponent___redArg___lam__1(v_a_9_, v_b_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__0, &lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__0_once, _init_lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__0);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2(lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__1, &lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__1_once, _init_lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___closed__1);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2___boxed(lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_Orbital_numeratorExponent___redArg___lam__2(v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent___redArg(lean_object* v_inst_23_, lean_object* v_00_u03b5_24_, lean_object* v_l_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
lean_inc_ref(v_l_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_GRH_New_Orbital_numeratorExponent___redArg___lam__0), 2, 1);
lean_closure_set(v___f_27_, 0, v_l_25_);
v___f_28_ = ((lean_object*)(lp_GRH_New_Orbital_numeratorExponent___redArg___closed__0));
v___f_29_ = ((lean_object*)(lp_GRH_New_Orbital_numeratorExponent___redArg___closed__1));
v___x_30_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_compactForm___boxed), 4, 3);
lean_closure_set(v___x_30_, 0, lean_box(0));
lean_closure_set(v___x_30_, 1, v_00_u03b5_24_);
lean_closure_set(v___x_30_, 2, v___f_27_);
lean_inc(v_i_26_);
lean_inc(v_inst_23_);
v___x_31_ = lp_GRH_New_paramAddRho___redArg(v_inst_23_, v_l_25_, v_i_26_);
v___x_32_ = lp_GRH_New_HCParam_lowerCount___redArg(v_inst_23_, v___f_29_, v___x_30_, v___f_28_, v_i_26_);
v___x_33_ = lean_int_add(v___x_31_, v___x_32_);
lean_dec(v___x_32_);
lean_dec(v___x_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_numeratorExponent(lean_object* v_n_34_, lean_object* v_inst_35_, lean_object* v_00_u03b5_36_, lean_object* v_l_37_, lean_object* v_i_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_GRH_New_Orbital_numeratorExponent___redArg(v_inst_35_, v_00_u03b5_36_, v_l_37_, v_i_38_);
return v___x_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Character_MultiplicityOrbitalIntegral(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Character_OpenOrbitIntegral(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Character_FormalDegree(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Character_MultiplicityOrbitalIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Character_OpenOrbitIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
