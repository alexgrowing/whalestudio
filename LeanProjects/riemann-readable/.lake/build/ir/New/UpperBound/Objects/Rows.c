// Lean compiler output
// Module: New.UpperBound.Objects.Rows
// Imports: public import Init public meta import Init public import Lib.Weil.Seesaw public import New.UpperBound.Objects.AuxiliaryPair public import New.UpperBound.Objects.Columns public import New.UpperBound.Objects.Parameters
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
lean_object* lp_GRH_New_Data_gridCentres___redArg(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Function_Embedding_inl___redArg___lam__0(lean_object*);
static const lean_closure_object lp_GRH_New_Data_inclY___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Function_Embedding_inl___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Data_inclY___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Data_inclY___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY___redArg(){
_start:
{
lean_object* v___f_3_; 
v___f_3_ = ((lean_object*)(lp_GRH_New_Data_inclY___redArg___closed__0));
return v___f_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_GRH_New_Data_inclY___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY(lean_object* v_P_6_, lean_object* v_D_7_, lean_object* v_j_8_){
_start:
{
lean_object* v___f_9_; 
v___f_9_ = ((lean_object*)(lp_GRH_New_Data_inclY___redArg___closed__0));
return v___f_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_inclY___boxed(lean_object* v_P_10_, lean_object* v_D_11_, lean_object* v_j_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH_New_Data_inclY(v_P_10_, v_D_11_, v_j_12_);
lean_dec(v_j_12_);
lean_dec_ref(v_D_11_);
lean_dec_ref(v_P_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres___redArg(lean_object* v_D_14_, lean_object* v_00_u03c4_15_, lean_object* v_j_16_){
_start:
{
uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v_centre_19_; lean_object* v_length_20_; lean_object* v_isUp_21_; lean_object* v_stem_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_34_; 
v___x_17_ = 0;
v___x_18_ = lp_GRH_New_Data_gridCentres___redArg(v_D_14_, v_00_u03c4_15_, v___x_17_);
v_centre_19_ = lean_ctor_get(v___x_18_, 1);
v_length_20_ = lean_ctor_get(v___x_18_, 2);
v_isUp_21_ = lean_ctor_get(v___x_18_, 3);
v_stem_22_ = lean_ctor_get(v___x_18_, 4);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_34_ == 0)
{
lean_object* v_unused_35_; 
v_unused_35_ = lean_ctor_get(v___x_18_, 0);
lean_dec(v_unused_35_);
v___x_24_ = v___x_18_;
v_isShared_25_ = v_isSharedCheck_34_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_stem_22_);
lean_inc(v_isUp_21_);
lean_inc(v_length_20_);
lean_inc(v_centre_19_);
lean_dec(v___x_18_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_34_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_sub(v_j_16_, v___x_26_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_30_);
v___x_32_ = v___x_24_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_centre_19_);
lean_ctor_set(v_reuseFailAlloc_33_, 2, v_length_20_);
lean_ctor_set(v_reuseFailAlloc_33_, 3, v_isUp_21_);
lean_ctor_set(v_reuseFailAlloc_33_, 4, v_stem_22_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres___redArg___boxed(lean_object* v_D_36_, lean_object* v_00_u03c4_37_, lean_object* v_j_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_GRH_New_Data_descentCentres___redArg(v_D_36_, v_00_u03c4_37_, v_j_38_);
lean_dec(v_j_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres(lean_object* v_P_40_, lean_object* v_D_41_, lean_object* v_00_u03c4_42_, lean_object* v_j_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_GRH_New_Data_descentCentres___redArg(v_D_41_, v_00_u03c4_42_, v_j_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_descentCentres___boxed(lean_object* v_P_45_, lean_object* v_D_46_, lean_object* v_00_u03c4_47_, lean_object* v_j_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH_New_Data_descentCentres(v_P_45_, v_D_46_, v_00_u03c4_47_, v_j_48_);
lean_dec(v_j_48_);
lean_dec_ref(v_P_45_);
return v_res_49_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Seesaw(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_AuxiliaryPair(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Columns(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Parameters(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Seesaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_AuxiliaryPair(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Columns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Parameters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
