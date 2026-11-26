// Lean compiler output
// Module: Lib.LocalGL.Green.HallAlgebra
// Imports: public import Init public meta import Init public import Lib.General.Groups.BesselGroups public import Lib.General.Groups.CharacterTheory
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
extern lean_object* lp_mathlib_Real_instAddMonoid;
lean_object* lp_mathlib_NSMul_toSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Prod_instAddMonoid___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_AddZeroClass_toAddZero___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_prod___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_coprod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_mapQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_restrict___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_instAddGroup;
lean_object* lp_mathlib_ZSMul_toSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__0 = (const lean_object*)&lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__0_value)} };
static const lean_object* lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__1 = (const lean_object*)&lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_instModuleComplexHall___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instModuleComplexHall___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_instModuleComplexHall___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnSub___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnQuot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Hall_constOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Hall_constOne___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Hall_constOne___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Hall_constOne___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0, &lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0_once, _init_lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GRH_New_instAddCommGroupHall___aux__1___redArg();
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1(lean_object* v_k_7_, lean_object* v_inst_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0, &lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0_once, _init_lp_GRH_New_instAddCommGroupHall___aux__1___redArg___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__1___boxed(lean_object* v_k_11_, lean_object* v_inst_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_instAddCommGroupHall___aux__1(v_k_11_, v_inst_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec_ref(v_inst_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__3___redArg(lean_object* v_f_15_, lean_object* v_g_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___x_18_; lean_object* v_re_19_; lean_object* v_im_20_; lean_object* v___x_21_; lean_object* v_re_22_; lean_object* v_im_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_32_; 
lean_inc(v_i_17_);
v___x_18_ = lean_apply_1(v_f_15_, v_i_17_);
v_re_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_re_19_);
v_im_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_im_20_);
lean_dec_ref(v___x_18_);
v___x_21_ = lean_apply_1(v_g_16_, v_i_17_);
v_re_22_ = lean_ctor_get(v___x_21_, 0);
v_im_23_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_32_ == 0)
{
v___x_25_ = v___x_21_;
v_isShared_26_ = v_isSharedCheck_32_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_im_23_);
lean_inc(v_re_22_);
lean_dec(v___x_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_32_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_30_; 
v___f_27_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_27_, 0, v_re_19_);
lean_closure_set(v___f_27_, 1, v_re_22_);
v___f_28_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_28_, 0, v_im_20_);
lean_closure_set(v___f_28_, 1, v_im_23_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___f_28_);
lean_ctor_set(v___x_25_, 0, v___f_27_);
v___x_30_ = v___x_25_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___f_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___f_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__3(lean_object* v_k_33_, lean_object* v_inst_34_, lean_object* v_f_35_, lean_object* v_g_36_, lean_object* v_i_37_){
_start:
{
lean_object* v___x_38_; lean_object* v_re_39_; lean_object* v_im_40_; lean_object* v___x_41_; lean_object* v_re_42_; lean_object* v_im_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_52_; 
lean_inc(v_i_37_);
v___x_38_ = lean_apply_1(v_f_35_, v_i_37_);
v_re_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_re_39_);
v_im_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_im_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = lean_apply_1(v_g_36_, v_i_37_);
v_re_42_ = lean_ctor_get(v___x_41_, 0);
v_im_43_ = lean_ctor_get(v___x_41_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_52_ == 0)
{
v___x_45_ = v___x_41_;
v_isShared_46_ = v_isSharedCheck_52_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_im_43_);
lean_inc(v_re_42_);
lean_dec(v___x_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_52_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_50_; 
v___f_47_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_47_, 0, v_re_39_);
lean_closure_set(v___f_47_, 1, v_re_42_);
v___f_48_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_48_, 0, v_im_40_);
lean_closure_set(v___f_48_, 1, v_im_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___f_48_);
lean_ctor_set(v___x_45_, 0, v___f_47_);
v___x_50_ = v___x_45_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___f_47_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v___f_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__3___boxed(lean_object* v_k_53_, lean_object* v_inst_54_, lean_object* v_f_55_, lean_object* v_g_56_, lean_object* v_i_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_GRH_New_instAddCommGroupHall___aux__3(v_k_53_, v_inst_54_, v_f_55_, v_g_56_, v_i_57_);
lean_dec_ref(v_inst_54_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__8___redArg(lean_object* v_n_59_, lean_object* v_x_60_, lean_object* v_i_61_){
_start:
{
lean_object* v___x_62_; lean_object* v_toNSMul_63_; lean_object* v___x_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_62_ = lp_mathlib_Real_instAddMonoid;
v_toNSMul_63_ = lean_ctor_get(v___x_62_, 2);
v___x_64_ = lean_apply_1(v_x_60_, v_i_61_);
lean_inc(v_toNSMul_63_);
v___f_65_ = lean_alloc_closure((void*)(lp_mathlib_NSMul_toSMul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_65_, 0, v_toNSMul_63_);
v___x_66_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_67_ = lp_mathlib_Complex_mulAux___redArg(v___f_65_, v_n_59_, v___x_66_, v___x_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__8(lean_object* v_k_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_x_71_, lean_object* v_i_72_){
_start:
{
lean_object* v___x_73_; lean_object* v_toNSMul_74_; lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_73_ = lp_mathlib_Real_instAddMonoid;
v_toNSMul_74_ = lean_ctor_get(v___x_73_, 2);
v___x_75_ = lean_apply_1(v_x_71_, v_i_72_);
lean_inc(v_toNSMul_74_);
v___f_76_ = lean_alloc_closure((void*)(lp_mathlib_NSMul_toSMul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_76_, 0, v_toNSMul_74_);
v___x_77_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_78_ = lp_mathlib_Complex_mulAux___redArg(v___f_76_, v_n_70_, v___x_77_, v___x_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__8___boxed(lean_object* v_k_79_, lean_object* v_inst_80_, lean_object* v_n_81_, lean_object* v_x_82_, lean_object* v_i_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lp_GRH_New_instAddCommGroupHall___aux__8(v_k_79_, v_inst_80_, v_n_81_, v_x_82_, v_i_83_);
lean_dec_ref(v_inst_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__12___redArg(lean_object* v_f_85_, lean_object* v_i_86_){
_start:
{
lean_object* v___x_87_; lean_object* v_re_88_; lean_object* v_im_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_98_; 
v___x_87_ = lean_apply_1(v_f_85_, v_i_86_);
v_re_88_ = lean_ctor_get(v___x_87_, 0);
v_im_89_ = lean_ctor_get(v___x_87_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_98_ == 0)
{
v___x_91_ = v___x_87_;
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_im_89_);
lean_inc(v_re_88_);
lean_dec(v___x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_96_; 
v___f_93_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_93_, 0, v_re_88_);
v___f_94_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_94_, 0, v_im_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___f_94_);
lean_ctor_set(v___x_91_, 0, v___f_93_);
v___x_96_ = v___x_91_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___f_93_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___f_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__12(lean_object* v_k_99_, lean_object* v_inst_100_, lean_object* v_f_101_, lean_object* v_i_102_){
_start:
{
lean_object* v___x_103_; lean_object* v_re_104_; lean_object* v_im_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_114_; 
v___x_103_ = lean_apply_1(v_f_101_, v_i_102_);
v_re_104_ = lean_ctor_get(v___x_103_, 0);
v_im_105_ = lean_ctor_get(v___x_103_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_114_ == 0)
{
v___x_107_ = v___x_103_;
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_im_105_);
lean_inc(v_re_104_);
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___x_112_; 
v___f_109_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_109_, 0, v_re_104_);
v___f_110_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_110_, 0, v_im_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___f_110_);
lean_ctor_set(v___x_107_, 0, v___f_109_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___f_109_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___f_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__12___boxed(lean_object* v_k_115_, lean_object* v_inst_116_, lean_object* v_f_117_, lean_object* v_i_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_GRH_New_instAddCommGroupHall___aux__12(v_k_115_, v_inst_116_, v_f_117_, v_i_118_);
lean_dec_ref(v_inst_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__14___redArg(lean_object* v_f_120_, lean_object* v_g_121_, lean_object* v_i_122_){
_start:
{
lean_object* v___x_123_; lean_object* v_re_124_; lean_object* v_im_125_; lean_object* v___x_126_; lean_object* v_re_127_; lean_object* v_im_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_139_; 
lean_inc(v_i_122_);
v___x_123_ = lean_apply_1(v_f_120_, v_i_122_);
v_re_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_re_124_);
v_im_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_im_125_);
lean_dec_ref(v___x_123_);
v___x_126_ = lean_apply_1(v_g_121_, v_i_122_);
v_re_127_ = lean_ctor_get(v___x_126_, 0);
v_im_128_ = lean_ctor_get(v___x_126_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_139_ == 0)
{
v___x_130_ = v___x_126_;
v_isShared_131_ = v_isSharedCheck_139_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_im_128_);
lean_inc(v_re_127_);
lean_dec(v___x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_139_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_137_; 
v___f_132_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_132_, 0, v_re_127_);
v___f_133_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_133_, 0, v_re_124_);
lean_closure_set(v___f_133_, 1, v___f_132_);
v___f_134_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_134_, 0, v_im_128_);
v___f_135_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_135_, 0, v_im_125_);
lean_closure_set(v___f_135_, 1, v___f_134_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___f_135_);
lean_ctor_set(v___x_130_, 0, v___f_133_);
v___x_137_ = v___x_130_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___f_133_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___f_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__14(lean_object* v_k_140_, lean_object* v_inst_141_, lean_object* v_f_142_, lean_object* v_g_143_, lean_object* v_i_144_){
_start:
{
lean_object* v___x_145_; lean_object* v_re_146_; lean_object* v_im_147_; lean_object* v___x_148_; lean_object* v_re_149_; lean_object* v_im_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_161_; 
lean_inc(v_i_144_);
v___x_145_ = lean_apply_1(v_f_142_, v_i_144_);
v_re_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_re_146_);
v_im_147_ = lean_ctor_get(v___x_145_, 1);
lean_inc(v_im_147_);
lean_dec_ref(v___x_145_);
v___x_148_ = lean_apply_1(v_g_143_, v_i_144_);
v_re_149_ = lean_ctor_get(v___x_148_, 0);
v_im_150_ = lean_ctor_get(v___x_148_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_161_ == 0)
{
v___x_152_ = v___x_148_;
v_isShared_153_ = v_isSharedCheck_161_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_im_150_);
lean_inc(v_re_149_);
lean_dec(v___x_148_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_161_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_159_; 
v___f_154_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_154_, 0, v_re_149_);
v___f_155_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_155_, 0, v_re_146_);
lean_closure_set(v___f_155_, 1, v___f_154_);
v___f_156_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_156_, 0, v_im_150_);
v___f_157_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_157_, 0, v_im_147_);
lean_closure_set(v___f_157_, 1, v___f_156_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___f_157_);
lean_ctor_set(v___x_152_, 0, v___f_155_);
v___x_159_ = v___x_152_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___f_155_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___f_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__14___boxed(lean_object* v_k_162_, lean_object* v_inst_163_, lean_object* v_f_164_, lean_object* v_g_165_, lean_object* v_i_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lp_GRH_New_instAddCommGroupHall___aux__14(v_k_162_, v_inst_163_, v_f_164_, v_g_165_, v_i_166_);
lean_dec_ref(v_inst_163_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__16___redArg(lean_object* v_z_168_, lean_object* v_x_169_, lean_object* v_i_170_){
_start:
{
lean_object* v___x_171_; lean_object* v_toZSMul_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = lp_mathlib_Real_instAddGroup;
v_toZSMul_172_ = lean_ctor_get(v___x_171_, 3);
v___x_173_ = lean_apply_1(v_x_169_, v_i_170_);
lean_inc(v_toZSMul_172_);
v___f_174_ = lean_alloc_closure((void*)(lp_mathlib_ZSMul_toSMul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_174_, 0, v_toZSMul_172_);
v___x_175_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_176_ = lp_mathlib_Complex_mulAux___redArg(v___f_174_, v_z_168_, v___x_175_, v___x_173_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__16(lean_object* v_k_177_, lean_object* v_inst_178_, lean_object* v_z_179_, lean_object* v_x_180_, lean_object* v_i_181_){
_start:
{
lean_object* v___x_182_; lean_object* v_toZSMul_183_; lean_object* v___x_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = lp_mathlib_Real_instAddGroup;
v_toZSMul_183_ = lean_ctor_get(v___x_182_, 3);
v___x_184_ = lean_apply_1(v_x_180_, v_i_181_);
lean_inc(v_toZSMul_183_);
v___f_185_ = lean_alloc_closure((void*)(lp_mathlib_ZSMul_toSMul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_185_, 0, v_toZSMul_183_);
v___x_186_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_187_ = lp_mathlib_Complex_mulAux___redArg(v___f_185_, v_z_179_, v___x_186_, v___x_184_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instAddCommGroupHall___aux__16___boxed(lean_object* v_k_188_, lean_object* v_inst_189_, lean_object* v_z_190_, lean_object* v_x_191_, lean_object* v_i_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = lp_GRH_New_instAddCommGroupHall___aux__16(v_k_188_, v_inst_189_, v_z_190_, v_x_191_, v_i_192_);
lean_dec_ref(v_inst_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instModuleComplexHall___aux__1___redArg(lean_object* v_a_197_, lean_object* v_f_198_, lean_object* v_i_199_){
_start:
{
lean_object* v_re_200_; lean_object* v_im_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_204_; 
v_re_200_ = lean_ctor_get(v_a_197_, 0);
lean_inc(v_re_200_);
v_im_201_ = lean_ctor_get(v_a_197_, 1);
lean_inc(v_im_201_);
lean_dec_ref(v_a_197_);
v___x_202_ = lean_apply_1(v_f_198_, v_i_199_);
v___f_203_ = ((lean_object*)(lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__1));
v___x_204_ = lp_mathlib_Complex_mulAux___redArg(v___f_203_, v_re_200_, v_im_201_, v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instModuleComplexHall___aux__1(lean_object* v_k_205_, lean_object* v_inst_206_, lean_object* v_a_207_, lean_object* v_f_208_, lean_object* v_i_209_){
_start:
{
lean_object* v_re_210_; lean_object* v_im_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; 
v_re_210_ = lean_ctor_get(v_a_207_, 0);
lean_inc(v_re_210_);
v_im_211_ = lean_ctor_get(v_a_207_, 1);
lean_inc(v_im_211_);
lean_dec_ref(v_a_207_);
v___x_212_ = lean_apply_1(v_f_208_, v_i_209_);
v___f_213_ = ((lean_object*)(lp_GRH_New_instModuleComplexHall___aux__1___redArg___closed__1));
v___x_214_ = lp_mathlib_Complex_mulAux___redArg(v___f_213_, v_re_210_, v_im_211_, v___x_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instModuleComplexHall___aux__1___boxed(lean_object* v_k_215_, lean_object* v_inst_216_, lean_object* v_a_217_, lean_object* v_f_218_, lean_object* v_i_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = lp_GRH_New_instModuleComplexHall___aux__1(v_k_215_, v_inst_216_, v_a_217_, v_f_218_, v_i_219_);
lean_dec_ref(v_inst_216_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnSub___redArg(lean_object* v_g_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lp_mathlib_LinearMap_restrict___redArg(v_g_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnSub(lean_object* v_k_223_, lean_object* v_inst_224_, lean_object* v_V_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_g_228_, lean_object* v_W_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lp_mathlib_LinearMap_restrict___redArg(v_g_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnSub___boxed(lean_object* v_k_231_, lean_object* v_inst_232_, lean_object* v_V_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_g_236_, lean_object* v_W_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = lp_GRH_New_StableSubspace_endOnSub(v_k_231_, v_inst_232_, v_V_233_, v_inst_234_, v_inst_235_, v_g_236_, v_W_237_);
lean_dec(v_inst_235_);
lean_dec_ref(v_inst_234_);
lean_dec_ref(v_inst_232_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnQuot___redArg(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_g_242_, lean_object* v_W_243_){
_start:
{
lean_object* v___x_244_; lean_object* v_toRing_245_; lean_object* v___x_246_; 
v___x_244_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_239_);
v_toRing_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref(v_toRing_245_);
lean_dec_ref(v___x_244_);
v___x_246_ = lp_mathlib_Submodule_mapQ___redArg(v_toRing_245_, v_inst_240_, v_inst_241_, v_W_243_, v_g_242_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_endOnQuot(lean_object* v_k_247_, lean_object* v_inst_248_, lean_object* v_V_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_g_252_, lean_object* v_W_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lp_GRH_New_StableSubspace_endOnQuot___redArg(v_inst_248_, v_inst_250_, v_inst_251_, v_g_252_, v_W_253_);
return v___x_254_;
}
}
static lean_object* _init_lp_GRH_New_Hall_constOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_256_ = lp_mathlib_Complex_ofReal(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne___redArg(){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&lp_GRH_New_Hall_constOne___redArg___closed__0, &lp_GRH_New_Hall_constOne___redArg___closed__0_once, _init_lp_GRH_New_Hall_constOne___redArg___closed__0);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne___redArg___boxed(lean_object* v___dummy_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = lp_GRH_New_Hall_constOne___redArg();
return v_res_260_;
}
}
static lean_object* _init_lp_GRH_New_Hall_constOne___closed__0(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lp_GRH_New_Hall_constOne___redArg();
return v___x_261_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne(lean_object* v_k_262_, lean_object* v_inst_263_, lean_object* v_x_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&lp_GRH_New_Hall_constOne___closed__0, &lp_GRH_New_Hall_constOne___closed__0_once, _init_lp_GRH_New_Hall_constOne___closed__0);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Hall_constOne___boxed(lean_object* v_k_266_, lean_object* v_inst_267_, lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_GRH_New_Hall_constOne(v_k_266_, v_inst_267_, v_x_268_);
lean_dec(v_x_268_);
lean_dec_ref(v_inst_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___redArg___lam__0(lean_object* v_toZero_270_, lean_object* v_x_271_){
_start:
{
lean_inc(v_toZero_270_);
return v_toZero_270_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___redArg___lam__0___boxed(lean_object* v_toZero_272_, lean_object* v_x_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = lp_GRH_New_blockTriangularEnd___redArg___lam__0(v_toZero_272_, v_x_273_);
lean_dec(v_x_273_);
lean_dec(v_toZero_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___redArg(lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_toAddMonoid_280_; lean_object* v_toAddMonoid_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_toZero_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_toAddMonoid_280_ = lean_ctor_get(v_inst_276_, 0);
lean_inc_ref_n(v_toAddMonoid_280_, 2);
lean_dec_ref(v_inst_276_);
v_toAddMonoid_281_ = lean_ctor_get(v_inst_275_, 0);
lean_inc_ref(v_toAddMonoid_281_);
lean_dec_ref(v_inst_275_);
v___x_282_ = lp_mathlib_Prod_instAddMonoid___redArg(v_toAddMonoid_280_, v_toAddMonoid_281_);
v___x_283_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_280_);
lean_dec_ref(v_toAddMonoid_280_);
v___x_284_ = lp_mathlib_AddZeroClass_toAddZero___redArg(v___x_283_);
v_toZero_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_toZero_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = lp_mathlib_LinearMap_prod___redArg(v_b_278_, v_x_279_);
v___f_287_ = lean_alloc_closure((void*)(lp_GRH_New_blockTriangularEnd___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_287_, 0, v_toZero_285_);
v___x_288_ = lp_mathlib_LinearMap_prod___redArg(v___f_287_, v_a_277_);
v___x_289_ = lp_mathlib_LinearMap_coprod___redArg(v___x_282_, v___x_286_, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd(lean_object* v_k_290_, lean_object* v_V_291_, lean_object* v_V_x27_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v_x_300_){
_start:
{
lean_object* v_toAddMonoid_301_; lean_object* v_toAddMonoid_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_toZero_306_; lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_toAddMonoid_301_ = lean_ctor_get(v_inst_296_, 0);
lean_inc_ref_n(v_toAddMonoid_301_, 2);
lean_dec_ref(v_inst_296_);
v_toAddMonoid_302_ = lean_ctor_get(v_inst_294_, 0);
lean_inc_ref(v_toAddMonoid_302_);
lean_dec_ref(v_inst_294_);
v___x_303_ = lp_mathlib_Prod_instAddMonoid___redArg(v_toAddMonoid_301_, v_toAddMonoid_302_);
v___x_304_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_301_);
lean_dec_ref(v_toAddMonoid_301_);
v___x_305_ = lp_mathlib_AddZeroClass_toAddZero___redArg(v___x_304_);
v_toZero_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_toZero_306_);
lean_dec_ref(v___x_305_);
v___x_307_ = lp_mathlib_LinearMap_prod___redArg(v_b_299_, v_x_300_);
v___f_308_ = lean_alloc_closure((void*)(lp_GRH_New_blockTriangularEnd___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_308_, 0, v_toZero_306_);
v___x_309_ = lp_mathlib_LinearMap_prod___redArg(v___f_308_, v_a_298_);
v___x_310_ = lp_mathlib_LinearMap_coprod___redArg(v___x_303_, v___x_307_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockTriangularEnd___boxed(lean_object* v_k_311_, lean_object* v_V_312_, lean_object* v_V_x27_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_a_319_, lean_object* v_b_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = lp_GRH_New_blockTriangularEnd(v_k_311_, v_V_312_, v_V_x27_313_, v_inst_314_, v_inst_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_a_319_, v_b_320_, v_x_321_);
lean_dec(v_inst_318_);
lean_dec(v_inst_316_);
lean_dec_ref(v_inst_314_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap___redArg(){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap___redArg___boxed(lean_object* v___dummy_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = lp_GRH_New_StableSubspace_comap___redArg();
return v_res_326_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap(lean_object* v_k_327_, lean_object* v_V_328_, lean_object* v_V_x27_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_g_335_, lean_object* v_g_x27_336_, lean_object* v_p_337_, lean_object* v_hp_338_, lean_object* v_U_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_StableSubspace_comap___boxed(lean_object* v_k_341_, lean_object* v_V_342_, lean_object* v_V_x27_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_g_349_, lean_object* v_g_x27_350_, lean_object* v_p_351_, lean_object* v_hp_352_, lean_object* v_U_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = lp_GRH_New_StableSubspace_comap(v_k_341_, v_V_342_, v_V_x27_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_g_349_, v_g_x27_350_, v_p_351_, v_hp_352_, v_U_353_);
lean_dec(v_p_351_);
lean_dec(v_g_x27_350_);
lean_dec(v_g_349_);
lean_dec(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
return v_res_354_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_BesselGroups(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_CharacterTheory(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_LocalGL_Green_HallAlgebra(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Groups_BesselGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Groups_CharacterTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
