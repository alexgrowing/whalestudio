// Lean compiler output
// Module: Lib.Shimura.Deformation.TangentBound
// Imports: public import Init public meta import Init public import Lib.General.Geometry.SerreTheorem public import Lib.Shimura.Deformation.TangentCount
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
lean_object* lp_mathlib_LinearMap_instZero___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_instSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toOppositeModule___redArg(lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_ring___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; lean_object* v_toSemiring_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; lean_object* v___x_7_; lean_object* v___f_8_; lean_object* v___x_9_; 
v___x_2_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_1_);
v_toSemiring_3_ = lean_ctor_get(v_inst_1_, 0);
v___x_4_ = lp_mathlib_LinearMap_addCommGroup___redArg(v___x_2_);
v___x_5_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
v___x_7_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toSemiring_3_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_8_, 0, v___x_7_);
v___x_9_ = lp_mathlib_TrivSqZeroExt_ring___redArg(v_inst_1_, v___x_4_, v___f_6_, v___f_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib(lean_object* v_k_10_, lean_object* v_M_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_C_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib___redArg(v_inst_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib___boxed(lean_object* v_k_19_, lean_object* v_M_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_C_24_, lean_object* v_inst_25_, lean_object* v_inst_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_GRH_New_Variety_TangentBound_instCommRingTrivSqZeroExtLinearMapId__lib(v_k_19_, v_M_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_C_24_, v_inst_25_, v_inst_26_);
lean_dec_ref(v_inst_26_);
lean_dec(v_inst_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__0(lean_object* v_00_u03c6_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_apply_1(v_00_u03c6_28_, v___y_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__1(lean_object* v_toAddCommMonoid_31_, lean_object* v_snd_32_, lean_object* v___f_33_, lean_object* v_toAdd_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_313__overap_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_313__overap_36_ = lp_mathlib_LinearMap_instZero___redArg(v_toAddCommMonoid_31_);
lean_inc(v___y_35_);
v___x_37_ = lean_apply_1(v___x_313__overap_36_, v___y_35_);
v___x_38_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v_snd_32_, v___f_33_, v___y_35_);
v___x_39_ = lean_apply_2(v_toAdd_34_, v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__1___boxed(lean_object* v_toAddCommMonoid_40_, lean_object* v_snd_41_, lean_object* v___f_42_, lean_object* v_toAdd_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__1(v_toAddCommMonoid_40_, v_snd_41_, v___f_42_, v_toAdd_43_, v___y_44_);
lean_dec_ref(v_toAddCommMonoid_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__2(lean_object* v_toAddCommMonoid_46_, lean_object* v_00_u03c6_47_, lean_object* v_toAdd_48_, lean_object* v_toZero_49_, lean_object* v___f_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_64_; 
v_fst_52_ = lean_ctor_get(v_x_51_, 0);
v_snd_53_ = lean_ctor_get(v_x_51_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_64_ == 0)
{
v___x_55_ = v_x_51_;
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_snd_53_);
lean_inc(v_fst_52_);
lean_dec(v_x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_toAdd_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___x_62_; 
v_toAdd_57_ = lean_ctor_get(v_toAddCommMonoid_46_, 1);
lean_inc(v_toAdd_57_);
v___x_58_ = lean_apply_1(v_00_u03c6_47_, v_fst_52_);
v___x_59_ = lean_apply_2(v_toAdd_48_, v___x_58_, v_toZero_49_);
v___f_60_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_60_, 0, v_toAddCommMonoid_46_);
lean_closure_set(v___f_60_, 1, v_snd_53_);
lean_closure_set(v___f_60_, 2, v___f_50_);
lean_closure_set(v___f_60_, 3, v_toAdd_57_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___f_60_);
lean_ctor_set(v___x_55_, 0, v___x_59_);
v___x_62_ = v___x_55_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___f_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg(lean_object* v_inst_65_, lean_object* v_00_u03c6_66_){
_start:
{
lean_object* v_toSemiring_67_; lean_object* v_toAddCommMonoid_68_; lean_object* v___x_69_; lean_object* v_toAdd_70_; lean_object* v___x_71_; lean_object* v_toZero_72_; lean_object* v___f_73_; lean_object* v___f_74_; 
v_toSemiring_67_ = lean_ctor_get(v_inst_65_, 0);
lean_inc_ref_n(v_toSemiring_67_, 2);
lean_dec_ref(v_inst_65_);
v_toAddCommMonoid_68_ = lean_ctor_get(v_toSemiring_67_, 0);
lean_inc_ref(v_toAddCommMonoid_68_);
v___x_69_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_67_);
v_toAdd_70_ = lean_ctor_get(v___x_69_, 1);
lean_inc(v_toAdd_70_);
lean_dec_ref(v___x_69_);
v___x_71_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_67_);
v_toZero_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_toZero_72_);
lean_dec_ref(v___x_71_);
lean_inc(v_00_u03c6_66_);
v___f_73_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_73_, 0, v_00_u03c6_66_);
v___f_74_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg___lam__2), 6, 5);
lean_closure_set(v___f_74_, 0, v_toAddCommMonoid_68_);
lean_closure_set(v___f_74_, 1, v_00_u03c6_66_);
lean_closure_set(v___f_74_, 2, v_toAdd_70_);
lean_closure_set(v___f_74_, 3, v_toZero_72_);
lean_closure_set(v___f_74_, 4, v___f_73_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap(lean_object* v_k_75_, lean_object* v_M_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_C_80_, lean_object* v_C_x27_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_00_u03c6_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_GRH_New_Variety_TangentBound_sqZeroMap___redArg(v_inst_84_, v_00_u03c6_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TangentBound_sqZeroMap___boxed(lean_object* v_k_88_, lean_object* v_M_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_C_93_, lean_object* v_C_x27_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_00_u03c6_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_GRH_New_Variety_TangentBound_sqZeroMap(v_k_88_, v_M_89_, v_inst_90_, v_inst_91_, v_inst_92_, v_C_93_, v_C_x27_94_, v_inst_95_, v_inst_96_, v_inst_97_, v_inst_98_, v_00_u03c6_99_);
lean_dec_ref(v_inst_98_);
lean_dec_ref(v_inst_96_);
lean_dec_ref(v_inst_95_);
lean_dec(v_inst_92_);
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_inst_90_);
return v_res_100_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Geometry_SerreTheorem(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Deformation_TangentCount(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_Deformation_TangentBound(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Geometry_SerreTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Deformation_TangentCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
