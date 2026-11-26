// Lean compiler output
// Module: Lib.PadicComparison.Crystalline.DividedPowerEnvelope
// Imports: public import Init public meta import Init public import Lib.PadicComparison.Completion public import Lib.PadicComparison.ToricTower
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_mk___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_semiring___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_frobenius___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Con_lift___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_frobModPd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Ideal_Quotient_mk___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_frobModPd___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_frobModPd___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobModPd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobModPd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobModPd___redArg(lean_object* v_p_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___f_7_; lean_object* v___f_8_; lean_object* v___f_9_; 
v___x_4_ = lean_box(0);
v___x_5_ = lp_mathlib_Ideal_Quotient_semiring___redArg(v_inst_3_, v___x_4_);
v___x_6_ = lp_mathlib_frobenius___redArg(v___x_5_, v_p_2_);
v___f_7_ = ((lean_object*)(lp_GRH_New_Variety_frobModPd___redArg___closed__0));
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_8_, 0, v___f_7_);
lean_closure_set(v___f_8_, 1, v___x_6_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Con_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_9_, 0, v___f_8_);
return v___f_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobModPd(lean_object* v_p_10_, lean_object* v_hp_11_, lean_object* v_S_12_, lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_GRH_New_Variety_frobModPd___redArg(v_p_10_, v_inst_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType___redArg(){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType___redArg___boxed(lean_object* v___dummy_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_GRH_New_Variety_instCoeSortCrysTestType___redArg();
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType(lean_object* v_p_20_, lean_object* v_hp_21_, lean_object* v_S_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_instCoeSortCrysTestType___boxed(lean_object* v_p_25_, lean_object* v_hp_26_, lean_object* v_S_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_GRH_New_Variety_instCoeSortCrysTestType(v_p_25_, v_hp_26_, v_S_27_, v_inst_28_);
lean_dec_ref(v_inst_28_);
lean_dec(v_p_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope___redArg(){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope___redArg___boxed(lean_object* v___dummy_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_Variety_preEnvelope___redArg();
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope(lean_object* v_T_34_, lean_object* v_inst_35_, lean_object* v_J_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_preEnvelope___boxed(lean_object* v_T_38_, lean_object* v_inst_39_, lean_object* v_J_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_GRH_New_Variety_preEnvelope(v_T_38_, v_inst_39_, v_J_40_);
lean_dec_ref(v_inst_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___redArg(lean_object* v_n_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
lean_object* v_zero_45_; uint8_t v_isZero_46_; 
v_zero_45_ = lean_unsigned_to_nat(0u);
v_isZero_46_ = lean_nat_dec_eq(v_n_42_, v_zero_45_);
if (v_isZero_46_ == 1)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_44_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__1_43_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_one_49_; lean_object* v_n_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_43_);
v_one_49_ = lean_unsigned_to_nat(1u);
v_n_50_ = lean_nat_sub(v_n_42_, v_one_49_);
v___x_51_ = lean_apply_1(v_h__2_44_, v_n_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___redArg___boxed(lean_object* v_n_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___redArg(v_n_52_, v_h__1_53_, v_h__2_54_);
lean_dec(v_n_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter(lean_object* v_motive_56_, lean_object* v_n_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
lean_object* v_zero_60_; uint8_t v_isZero_61_; 
v_zero_60_ = lean_unsigned_to_nat(0u);
v_isZero_61_ = lean_nat_dec_eq(v_n_57_, v_zero_60_);
if (v_isZero_61_ == 1)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_59_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__1_58_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v_one_64_; lean_object* v_n_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_58_);
v_one_64_ = lean_unsigned_to_nat(1u);
v_n_65_ = lean_nat_sub(v_n_57_, v_one_64_);
v___x_66_ = lean_apply_1(v_h__2_59_, v_n_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter___boxed(lean_object* v_motive_67_, lean_object* v_n_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_GRH___private_Lib_PadicComparison_Crystalline_DividedPowerEnvelope_0__New_Variety_koszulExact__pd__line_match__1__4_splitter(v_motive_67_, v_n_68_, v_h__1_69_, v_h__2_70_);
lean_dec(v_n_68_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_Completion(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_ToricTower(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicComparison_Crystalline_DividedPowerEnvelope(uint8_t builtin) {
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
res = initialize_GRH_Lib_PadicComparison_Completion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_ToricTower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
