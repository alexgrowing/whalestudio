// Lean compiler output
// Module: Lib.Weil.Periods.RealAndFinitePoints
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.BesselIntegral public import Lib.Weil.Periods.Equivariant
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
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___lam__1(lean_object*);
static const lean_closure_object lp_GRH_New_Grading_besselProdEquiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Grading_besselProdEquiv___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Grading_besselProdEquiv___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Grading_besselProdEquiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Grading_besselProdEquiv___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Grading_besselProdEquiv___redArg___closed__1_value;
static const lean_ctor_object lp_GRH_New_Grading_besselProdEquiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GRH_New_Grading_besselProdEquiv___redArg___closed__0_value),((lean_object*)&lp_GRH_New_Grading_besselProdEquiv___redArg___closed__1_value)}};
static const lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Grading_besselProdEquiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Grading_besselProdEquiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Grading_besselProdEquiv___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___lam__0(lean_object* v_z_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_fst_2_ = lean_ctor_get(v_z_1_, 0);
v_snd_3_ = lean_ctor_get(v_z_1_, 1);
v_isSharedCheck_10_ = !lean_is_exclusive(v_z_1_);
if (v_isSharedCheck_10_ == 0)
{
v___x_5_ = v_z_1_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_snd_3_);
lean_inc(v_fst_2_);
lean_dec(v_z_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_fst_2_);
lean_ctor_set(v_reuseFailAlloc_9_, 1, v_snd_3_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___lam__1(lean_object* v_r_11_){
_start:
{
lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_20_; 
v_fst_12_ = lean_ctor_get(v_r_11_, 0);
v_snd_13_ = lean_ctor_get(v_r_11_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v_r_11_);
if (v_isSharedCheck_20_ == 0)
{
v___x_15_ = v_r_11_;
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_snd_13_);
lean_inc(v_fst_12_);
lean_dec(v_r_11_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_fst_12_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_snd_13_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = ((lean_object*)(lp_GRH_New_Grading_besselProdEquiv___redArg___closed__2));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_GRH_New_Grading_besselProdEquiv___redArg();
return v_res_29_;
}
}
static lean_object* _init_lp_GRH_New_Grading_besselProdEquiv___closed__0(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_GRH_New_Grading_besselProdEquiv___redArg();
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv(lean_object* v_E_31_, lean_object* v_00_u03b9_32_, lean_object* v_X_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_s_39_, lean_object* v_00_u03b5_40_, lean_object* v_N_41_, lean_object* v_V_42_, lean_object* v_Y_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&lp_GRH_New_Grading_besselProdEquiv___closed__0, &lp_GRH_New_Grading_besselProdEquiv___closed__0_once, _init_lp_GRH_New_Grading_besselProdEquiv___closed__0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_besselProdEquiv___boxed(lean_object* v_E_45_, lean_object* v_00_u03b9_46_, lean_object* v_X_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_s_53_, lean_object* v_00_u03b5_54_, lean_object* v_N_55_, lean_object* v_V_56_, lean_object* v_Y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_GRH_New_Grading_besselProdEquiv(v_E_45_, v_00_u03b9_46_, v_X_47_, v_inst_48_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_, v_s_53_, v_00_u03b5_54_, v_N_55_, v_V_56_, v_Y_57_);
lean_dec_ref(v_Y_57_);
lean_dec_ref(v_V_56_);
lean_dec(v_N_55_);
lean_dec_ref(v_00_u03b5_54_);
lean_dec(v_s_53_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
lean_dec(v_inst_50_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
return v_res_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_BesselIntegral(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_Equivariant(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Periods_RealAndFinitePoints(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_BesselIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Periods_Equivariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
