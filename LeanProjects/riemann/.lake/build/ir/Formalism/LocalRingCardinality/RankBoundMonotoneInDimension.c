// Lean compiler output
// Module: Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.ThetaLiftIndependence.FinalThetaLiftAMFKIndep public import Formalism.FrobeniusOrbits.HostCorollaries public import Formalism.LocalRingCardinality.HostCls public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator public import Formalism.HarderNarasimhan.ShiftInvariance public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf public import Formalism.GradedWeylDivisibility.FinalB public import Formalism.GradedWeylDivisibility.FinalD public import Formalism.GradedWeylDivisibility.StatementE public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_divInvMonoid___redArg(lean_object*);
extern lean_object* lp_mathlib_PUnit_fintype;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__0;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__3___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__4___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__4(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BasicNotions_chainEx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_chainEx___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__0 = (const lean_object*)&lp_tree_Formalism_BasicNotions_chainEx___closed__0_value;
static const lean_closure_object lp_tree_Formalism_BasicNotions_chainEx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_chainEx___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__1 = (const lean_object*)&lp_tree_Formalism_BasicNotions_chainEx___closed__1_value;
static const lean_closure_object lp_tree_Formalism_BasicNotions_chainEx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_chainEx___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__2 = (const lean_object*)&lp_tree_Formalism_BasicNotions_chainEx___closed__2_value;
static const lean_closure_object lp_tree_Formalism_BasicNotions_chainEx___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_chainEx___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__3 = (const lean_object*)&lp_tree_Formalism_BasicNotions_chainEx___closed__3_value;
static const lean_closure_object lp_tree_Formalism_BasicNotions_chainEx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_chainEx___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__4 = (const lean_object*)&lp_tree_Formalism_BasicNotions_chainEx___closed__4_value;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__5;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_chainEx___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_chainEx___closed__6;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx;
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__0(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___lam__0___closed__0, &lp_tree_Formalism_BasicNotions_chainEx___lam__0___closed__0_once, _init_lp_tree_Formalism_BasicNotions_chainEx___lam__0___closed__0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_x_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_BasicNotions_chainEx___lam__0(v_x_9_, v_x_10_, v_x_11_, v___y_12_, v___y_13_);
lean_dec_ref(v___y_12_);
lean_dec(v_x_9_);
return v_res_14_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(2u);
v___x_16_ = lp_mathlib_ZMod_instField___redArg(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__0, &lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__0_once, _init_lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__0);
v___x_18_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__1(lean_object* v_i_19_, lean_object* v_c_20_){
_start:
{
lean_object* v___x_21_; lean_object* v_toRing_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_21_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__1, &lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__1_once, _init_lp_tree_Formalism_BasicNotions_chainEx___lam__1___closed__1);
v_toRing_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_toRing_22_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_22_);
v___x_24_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_23_);
lean_dec_ref(v___x_23_);
v___x_25_ = lp_mathlib_Multiplicative_divInvMonoid___redArg(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__1___boxed(lean_object* v_i_26_, lean_object* v_c_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_BasicNotions_chainEx___lam__1(v_i_26_, v_c_27_);
lean_dec(v_i_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__2(lean_object* v_x_29_, lean_object* v_x_30_, uint8_t v_00_u03c4_31_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__2___boxed(lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_00_u03c4_34_){
_start:
{
uint8_t v_00_u03c4_boxed_35_; lean_object* v_res_36_; 
v_00_u03c4_boxed_35_ = lean_unbox(v_00_u03c4_34_);
v_res_36_ = lp_tree_Formalism_BasicNotions_chainEx___lam__2(v_x_32_, v_x_33_, v_00_u03c4_boxed_35_);
lean_dec(v_x_32_);
return v_res_36_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___lam__3___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_38_ = lp_mathlib_Complex_ofReal(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__3(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___lam__3___closed__0, &lp_tree_Formalism_BasicNotions_chainEx___lam__3___closed__0_once, _init_lp_tree_Formalism_BasicNotions_chainEx___lam__3___closed__0);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__3___boxed(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_BasicNotions_chainEx___lam__3(v_x_42_, v_x_43_);
lean_dec(v_x_42_);
return v_res_44_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___lam__4___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__4(lean_object* v_x_47_, uint8_t v_x_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___lam__4___closed__0, &lp_tree_Formalism_BasicNotions_chainEx___lam__4___closed__0_once, _init_lp_tree_Formalism_BasicNotions_chainEx___lam__4___closed__0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__4___boxed(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_x_320__boxed_52_; lean_object* v_res_53_; 
v_x_320__boxed_52_ = lean_unbox(v_x_51_);
v_res_53_ = lp_tree_Formalism_BasicNotions_chainEx___lam__4(v_x_50_, v_x_320__boxed_52_);
lean_dec(v_x_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__5(lean_object* v___x_54_, lean_object* v_i_55_){
_start:
{
lean_inc(v___x_54_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_chainEx___lam__5___boxed(lean_object* v___x_56_, lean_object* v_i_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_BasicNotions_chainEx___lam__5(v___x_56_, v_i_57_);
lean_dec(v_i_57_);
lean_dec(v___x_56_);
return v_res_58_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___f_65_; 
v___x_64_ = lp_mathlib_PUnit_fintype;
v___f_65_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_chainEx___lam__5___boxed), 2, 1);
lean_closure_set(v___f_65_, 0, v___x_64_);
return v___f_65_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx___closed__6(void){
_start:
{
lean_object* v___f_66_; lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
v___f_66_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_chainEx___closed__4));
v___f_67_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_chainEx___closed__0));
v___f_68_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_chainEx___closed__3));
v___f_69_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_chainEx___closed__2));
v___x_70_ = lean_unsigned_to_nat(2u);
v___f_71_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_chainEx___closed__1));
v___f_72_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___closed__5, &lp_tree_Formalism_BasicNotions_chainEx___closed__5_once, _init_lp_tree_Formalism_BasicNotions_chainEx___closed__5);
v___x_73_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_73_, 0, v___f_72_);
lean_ctor_set(v___x_73_, 1, v___f_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
lean_ctor_set(v___x_73_, 3, v___f_69_);
lean_ctor_set(v___x_73_, 4, v___f_68_);
lean_ctor_set(v___x_73_, 5, v___f_68_);
lean_ctor_set(v___x_73_, 6, v___f_67_);
lean_ctor_set(v___x_73_, 7, v___f_66_);
lean_ctor_set(v___x_73_, 8, v___f_66_);
return v___x_73_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_chainEx(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_chainEx___closed__6, &lp_tree_Formalism_BasicNotions_chainEx___closed__6_once, _init_lp_tree_Formalism_BasicNotions_chainEx___closed__6);
return v___x_74_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_FinalThetaLiftAMFKIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_HostCls(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalB(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalD(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementE(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_KpqSubgroupCompact(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_FinalThetaLiftAMFKIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_HostCls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_KpqSubgroupCompact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Formalism_BasicNotions_chainEx = _init_lp_tree_Formalism_BasicNotions_chainEx();
lean_mark_persistent(lp_tree_Formalism_BasicNotions_chainEx);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
