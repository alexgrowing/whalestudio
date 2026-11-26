// Lean compiler output
// Module: Lib.Adelic.Unitary.Defs
// Imports: public import Init public meta import Init public import Lib.Adelic.Adeles.AdditiveCharacter public import Lib.Adelic.Hecke.Basic public import Lib.General.Topology
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_AddZeroClass_toAddZero___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_instCoeGfG___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instCoeGfG___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_instCoeGfG___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_instCoeGfG___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_instCoeGfG___redArg___closed__0 = (const lean_object*)&lp_GRH_New_instCoeGfG___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_localLevel___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_localLevel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_localLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_localLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_instCoeGfG___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_GRH_New_instCoeGfG___redArg___lam__0___closed__0, &lp_GRH_New_instCoeGfG___redArg___lam__0___closed__0_once, _init_lp_GRH_New_instCoeGfG___redArg___lam__0___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__0___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GRH_New_instCoeGfG___redArg___lam__0(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__1(lean_object* v_toSemiring_7_, lean_object* v_inst_8_, lean_object* v___f_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toAddMonoid_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_toZero_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_24_; 
v___x_11_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_7_);
v___x_12_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_11_);
v_toAddMonoid_13_ = lean_ctor_get(v___x_12_, 1);
lean_inc_ref(v_toAddMonoid_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_13_);
lean_dec_ref(v_toAddMonoid_13_);
v___x_15_ = lp_mathlib_AddZeroClass_toAddZero___redArg(v___x_14_);
v_toZero_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_15_, 1);
lean_dec(v_unused_25_);
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_toZero_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_20_, 0, lean_box(0));
lean_closure_set(v___x_20_, 1, lean_box(0));
lean_closure_set(v___x_20_, 2, v_inst_8_);
lean_closure_set(v___x_20_, 3, v_toZero_16_);
lean_closure_set(v___x_20_, 4, v___f_9_);
lean_inc_ref(v___x_20_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v___x_20_);
lean_ctor_set(v___x_18_, 0, v___x_20_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__1___boxed(lean_object* v_toSemiring_26_, lean_object* v_inst_27_, lean_object* v___f_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_instCoeGfG___redArg___lam__1(v_toSemiring_26_, v_inst_27_, v___f_28_, v_x_29_);
lean_dec(v_x_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg___lam__2(lean_object* v___f_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___f_31_);
lean_ctor_set(v___x_33_, 1, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___redArg(lean_object* v_inst_35_){
_start:
{
lean_object* v___x_36_; lean_object* v_toSemiring_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; 
v___x_36_ = lp_mathlib_Complex_commRing;
v_toSemiring_37_ = lean_ctor_get(v___x_36_, 0);
v___f_38_ = ((lean_object*)(lp_GRH_New_instCoeGfG___redArg___closed__0));
lean_inc_ref(v_toSemiring_37_);
v___f_39_ = lean_alloc_closure((void*)(lp_GRH_New_instCoeGfG___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_39_, 0, v_toSemiring_37_);
lean_closure_set(v___f_39_, 1, v_inst_35_);
lean_closure_set(v___f_39_, 2, v___f_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_GRH_New_instCoeGfG___redArg___lam__2), 2, 1);
lean_closure_set(v___f_40_, 0, v___f_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG(lean_object* v_E_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_n_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_s_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_GRH_New_instCoeGfG___redArg(v_inst_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instCoeGfG___boxed(lean_object* v_E_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_s_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_GRH_New_instCoeGfG(v_E_50_, v_inst_51_, v_inst_52_, v_n_53_, v_inst_54_, v_inst_55_, v_inst_56_, v_s_57_);
lean_dec_ref(v_s_57_);
lean_dec(v_inst_54_);
lean_dec_ref(v_inst_51_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_localLevel___redArg(){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_localLevel___redArg___boxed(lean_object* v___dummy_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_GRH_New_localLevel___redArg();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_localLevel(lean_object* v_E_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_S_70_, lean_object* v_K_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_localLevel___boxed(lean_object* v_E_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_n_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_S_80_, lean_object* v_K_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_GRH_New_localLevel(v_E_73_, v_inst_74_, v_inst_75_, v_n_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_S_80_, v_K_81_);
lean_dec_ref(v_K_81_);
lean_dec_ref(v_inst_78_);
lean_dec(v_inst_77_);
lean_dec_ref(v_inst_74_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice___redArg(){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice___redArg___boxed(lean_object* v___dummy_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_Space_baseLattice___redArg();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice(lean_object* v_E_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_n_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_s_93_, lean_object* v_V_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_box(0);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_baseLattice___boxed(lean_object* v_E_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_n_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_s_102_, lean_object* v_V_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_GRH_New_Space_baseLattice(v_E_96_, v_inst_97_, v_inst_98_, v_n_99_, v_inst_100_, v_inst_101_, v_s_102_, v_V_103_);
lean_dec_ref(v_V_103_);
lean_dec_ref(v_s_102_);
lean_dec_ref(v_inst_101_);
lean_dec(v_inst_100_);
lean_dec_ref(v_inst_98_);
lean_dec_ref(v_inst_97_);
return v_res_104_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Adeles_AdditiveCharacter(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Hecke_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Topology(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_Unitary_Defs(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Adeles_AdditiveCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Adelic_Hecke_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Topology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
