// Lean compiler output
// Module: New.Congruences.FirstOrder.KummerMaps
// Imports: public import Init public meta import Init public import Lib.ClassField.GreenbergWiles.RelationsModL public import Lib.GaloisRep.Main.Defs public import New.Congruences.FirstOrder.EvenClasses
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
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_cast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Selmer_primeBelowPlus___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_w_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_primeBelowPlus___boxed(lean_object* v_E_9_, lean_object* v_inst_10_, lean_object* v_w_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_Selmer_primeBelowPlus(v_E_9_, v_inst_10_, v_w_11_);
lean_dec_ref(v_inst_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL___redArg(lean_object* v_00_u2113_13_, lean_object* v_00_u03bd_14_, lean_object* v_00_u03c8_15_, lean_object* v_g_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toRing_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
lean_inc(v_00_u2113_13_);
v___x_17_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_13_);
v___x_18_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_17_);
v_toRing_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_toRing_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_19_);
v___x_21_ = lean_nat_pow(v_00_u2113_13_, v_00_u03bd_14_);
lean_dec(v_00_u2113_13_);
v___x_22_ = lean_apply_1(v_00_u03c8_15_, v_g_16_);
v___x_23_ = lp_mathlib_ZMod_cast___redArg(v___x_20_, v___x_21_, v___x_22_);
lean_dec(v___x_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL___redArg___boxed(lean_object* v_00_u2113_24_, lean_object* v_00_u03bd_25_, lean_object* v_00_u03c8_26_, lean_object* v_g_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_Selmer_reductionModL___redArg(v_00_u2113_24_, v_00_u03bd_25_, v_00_u03c8_26_, v_g_27_);
lean_dec(v_00_u03bd_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL(lean_object* v_00_u2113_29_, lean_object* v_inst_30_, lean_object* v_E_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_00_u03bd_34_, lean_object* v_00_u03c8_35_, lean_object* v_g_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_GRH_New_Selmer_reductionModL___redArg(v_00_u2113_29_, v_00_u03bd_34_, v_00_u03c8_35_, v_g_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_reductionModL___boxed(lean_object* v_00_u2113_38_, lean_object* v_inst_39_, lean_object* v_E_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_00_u03bd_43_, lean_object* v_00_u03c8_44_, lean_object* v_g_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_GRH_New_Selmer_reductionModL(v_00_u2113_38_, v_inst_39_, v_E_40_, v_inst_41_, v_inst_42_, v_00_u03bd_43_, v_00_u03c8_44_, v_g_45_);
lean_dec(v_00_u03bd_43_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions___redArg(){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions___redArg___boxed(lean_object* v___dummy_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_GRH_New_Selmer_kummerReductions___redArg();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions(lean_object* v_00_u2113_51_, lean_object* v_inst_52_, lean_object* v_E_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_00_u03bd_56_, lean_object* v_e_57_, lean_object* v_I_58_, lean_object* v_inst_59_, lean_object* v_x_60_, lean_object* v_hx_61_, lean_object* v_T_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_kummerReductions___boxed(lean_object* v_00_u2113_64_, lean_object* v_inst_65_, lean_object* v_E_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_00_u03bd_69_, lean_object* v_e_70_, lean_object* v_I_71_, lean_object* v_inst_72_, lean_object* v_x_73_, lean_object* v_hx_74_, lean_object* v_T_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_Selmer_kummerReductions(v_00_u2113_64_, v_inst_65_, v_E_66_, v_inst_67_, v_inst_68_, v_00_u03bd_69_, v_e_70_, v_I_71_, v_inst_72_, v_x_73_, v_hx_74_, v_T_75_);
lean_dec(v_T_75_);
lean_dec_ref(v_x_73_);
lean_dec(v_e_70_);
lean_dec(v_00_u03bd_69_);
lean_dec_ref(v_inst_68_);
lean_dec_ref(v_inst_67_);
lean_dec(v_00_u2113_64_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_RelationsModL(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Main_Defs(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_FirstOrder_EvenClasses(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_FirstOrder_KummerMaps(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_GreenbergWiles_RelationsModL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_Main_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_FirstOrder_EvenClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
