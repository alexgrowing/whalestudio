// Lean compiler output
// Module: New.Congruences.FirstOrder.OnePrime
// Imports: public import Init public meta import Init public import Lib.Weil.Unramified.HeckeGL
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd___redArg();
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Patching_weightedSum___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Patching_residueLineStabilizer___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer(lean_object* v_F_5_, lean_object* v_inst_6_, lean_object* v_N_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_residueLineStabilizer___boxed(lean_object* v_F_9_, lean_object* v_inst_10_, lean_object* v_N_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_Patching_residueLineStabilizer(v_F_9_, v_inst_10_, v_N_11_);
lean_dec(v_N_11_);
lean_dec_ref(v_inst_10_);
return v_res_12_;
}
}
static lean_object* _init_lp_GRH_New_Patching_weightedSum___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_mathlib_Multiplicative_toAdd___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__0(lean_object* v_c_14_, lean_object* v_f_15_, lean_object* v_00_u03c1_16_, lean_object* v_toZSMul_17_, lean_object* v_g_18_){
_start:
{
lean_object* v___x_19_; lean_object* v_toFun_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_19_ = lean_obj_once(&lp_GRH_New_Patching_weightedSum___redArg___lam__0___closed__0, &lp_GRH_New_Patching_weightedSum___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Patching_weightedSum___redArg___lam__0___closed__0);
v_toFun_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_g_18_);
v___x_21_ = lean_apply_1(v_c_14_, v_g_18_);
lean_inc(v_toFun_20_);
v___x_22_ = lean_apply_1(v_toFun_20_, v___x_21_);
v___x_23_ = lean_apply_1(v_f_15_, v___x_22_);
v___x_24_ = lean_apply_1(v_00_u03c1_16_, v_g_18_);
v___x_25_ = lean_apply_2(v_toZSMul_17_, v___x_23_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__1(lean_object* v_c_26_, lean_object* v_00_u03c1_27_, lean_object* v_toZSMul_28_, lean_object* v_toAddCommMonoid_29_, lean_object* v_inst_30_, lean_object* v_f_31_){
_start:
{
lean_object* v___f_32_; lean_object* v___x_33_; 
v___f_32_ = lean_alloc_closure((void*)(lp_GRH_New_Patching_weightedSum___redArg___lam__0), 5, 4);
lean_closure_set(v___f_32_, 0, v_c_26_);
lean_closure_set(v___f_32_, 1, v_f_31_);
lean_closure_set(v___f_32_, 2, v_00_u03c1_27_);
lean_closure_set(v___f_32_, 3, v_toZSMul_28_);
v___x_33_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_29_, v_inst_30_, v___f_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg___lam__1___boxed(lean_object* v_c_34_, lean_object* v_00_u03c1_35_, lean_object* v_toZSMul_36_, lean_object* v_toAddCommMonoid_37_, lean_object* v_inst_38_, lean_object* v_f_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_GRH_New_Patching_weightedSum___redArg___lam__1(v_c_34_, v_00_u03c1_35_, v_toZSMul_36_, v_toAddCommMonoid_37_, v_inst_38_, v_f_39_);
lean_dec_ref(v_toAddCommMonoid_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___redArg(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_00_u03c1_43_, lean_object* v_c_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toSemiring_47_; lean_object* v_toAddCommMonoid_48_; lean_object* v_toZSMul_49_; lean_object* v___f_50_; 
lean_inc_ref(v_inst_42_);
v___x_45_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_42_);
v___x_46_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_45_);
lean_dec_ref(v___x_45_);
v_toSemiring_47_ = lean_ctor_get(v_inst_42_, 0);
lean_inc_ref(v_toSemiring_47_);
lean_dec_ref(v_inst_42_);
v_toAddCommMonoid_48_ = lean_ctor_get(v_toSemiring_47_, 0);
lean_inc_ref(v_toAddCommMonoid_48_);
lean_dec_ref(v_toSemiring_47_);
v_toZSMul_49_ = lean_ctor_get(v___x_46_, 3);
lean_inc(v_toZSMul_49_);
lean_dec_ref(v___x_46_);
v___f_50_ = lean_alloc_closure((void*)(lp_GRH_New_Patching_weightedSum___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_50_, 0, v_c_44_);
lean_closure_set(v___f_50_, 1, v_00_u03c1_43_);
lean_closure_set(v___f_50_, 2, v_toZSMul_49_);
lean_closure_set(v___f_50_, 3, v_toAddCommMonoid_48_);
lean_closure_set(v___f_50_, 4, v_inst_41_);
return v___f_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum(lean_object* v_00_u0393_51_, lean_object* v_R_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_m_56_, lean_object* v_00_u03c1_57_, lean_object* v_c_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_GRH_New_Patching_weightedSum___redArg(v_inst_54_, v_inst_55_, v_00_u03c1_57_, v_c_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Patching_weightedSum___boxed(lean_object* v_00_u0393_60_, lean_object* v_R_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_m_65_, lean_object* v_00_u03c1_66_, lean_object* v_c_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_GRH_New_Patching_weightedSum(v_00_u0393_60_, v_R_61_, v_inst_62_, v_inst_63_, v_inst_64_, v_m_65_, v_00_u03c1_66_, v_c_67_);
lean_dec(v_m_65_);
lean_dec_ref(v_inst_62_);
return v_res_68_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_HeckeGL(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_FirstOrder_OnePrime(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Unramified_HeckeGL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
