// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataDIVDefs
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.DataDIV public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_BasicNotions_DV_MramL_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_BasicNotions_DV_MramL_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_MramL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_MramL___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_ur(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_wSz(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_wSz___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_srcPar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_srcPar___closed__0;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_srcPar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_srcPar___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_srcPar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___redArg___lam__0(lean_object* v_f_u2097_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_f_u2097_1_, v___y_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___redArg(lean_object* v_f_u2097_4_){
_start:
{
lean_object* v___f_5_; 
v___f_5_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5_, 0, v_f_u2097_4_);
return v___f_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0(lean_object* v___x_6_, lean_object* v___x_7_, lean_object* v___x_8_, lean_object* v_inst_9_, lean_object* v_f_u2097_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_f_u2097_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0___boxed(lean_object* v___x_12_, lean_object* v___x_13_, lean_object* v___x_14_, lean_object* v_inst_15_, lean_object* v_f_u2097_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_LinearMap_restrictScalars___at___00Formalism_BasicNotions_DV_MramL_spec__0(v___x_12_, v___x_13_, v___x_14_, v_inst_15_, v_f_u2097_16_);
lean_dec_ref(v___x_14_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v___x_12_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_BasicNotions_DV_MramL_spec__1(lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v___x_20_, lean_object* v_00_u03c3_u2081_u2082_21_, lean_object* v_f_22_, lean_object* v_p_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_BasicNotions_DV_MramL_spec__1___boxed(lean_object* v___x_25_, lean_object* v___x_26_, lean_object* v___x_27_, lean_object* v_00_u03c3_u2081_u2082_28_, lean_object* v_f_29_, lean_object* v_p_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Submodule_comap___at___00Formalism_BasicNotions_DV_MramL_spec__1(v___x_25_, v___x_26_, v___x_27_, v_00_u03c3_u2081_u2082_28_, v_f_29_, v_p_30_);
lean_dec(v_f_29_);
lean_dec(v_00_u03c3_u2081_u2082_28_);
lean_dec_ref(v___x_27_);
lean_dec_ref(v___x_26_);
lean_dec_ref(v___x_25_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_MramL(lean_object* v_D_32_, lean_object* v_u_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_MramL___boxed(lean_object* v_D_35_, lean_object* v_u_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_BasicNotions_DV_MramL(v_D_35_, v_u_36_);
lean_dec(v_u_36_);
lean_dec_ref(v_D_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_ur(lean_object* v_D_38_, lean_object* v_w_39_, lean_object* v_y_40_){
_start:
{
lean_object* v_what_u2082_41_; lean_object* v_places_42_; lean_object* v_ramIdx_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___f_46_; 
v_what_u2082_41_ = lean_ctor_get(v_D_38_, 4);
lean_inc_ref(v_what_u2082_41_);
lean_dec_ref(v_D_38_);
v_places_42_ = lean_ctor_get(v_what_u2082_41_, 2);
lean_inc_ref(v_places_42_);
lean_dec_ref(v_what_u2082_41_);
v_ramIdx_43_ = lean_ctor_get(v_places_42_, 3);
lean_inc_ref(v_ramIdx_43_);
lean_dec_ref(v_places_42_);
v___x_44_ = lean_apply_1(v_ramIdx_43_, v_w_39_);
v___x_45_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_44_);
v___f_46_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_46_, 0, v___x_45_);
lean_closure_set(v___f_46_, 1, v_y_40_);
return v___f_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_wSz(lean_object* v_D_47_, lean_object* v_j_48_, lean_object* v_00_u03c1_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_dec_le(v___x_50_, v_j_48_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec(v_00_u03c1_49_);
lean_dec_ref(v_D_47_);
v___x_52_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_52_;
}
else
{
lean_object* v_R_53_; lean_object* v_hc_54_; lean_object* v_m_55_; uint8_t v___x_56_; 
v_R_53_ = lean_ctor_get(v_D_47_, 0);
lean_inc_ref(v_R_53_);
v_hc_54_ = lean_ctor_get(v_D_47_, 6);
lean_inc_ref(v_hc_54_);
lean_dec_ref(v_D_47_);
v_m_55_ = lean_ctor_get(v_R_53_, 2);
lean_inc(v_m_55_);
lean_dec_ref(v_R_53_);
v___x_56_ = lean_nat_dec_le(v_j_48_, v_m_55_);
lean_dec(v_m_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v_hc_54_);
lean_dec(v_00_u03c1_49_);
v___x_57_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v_e_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; 
v___x_58_ = lean_apply_1(v_hc_54_, v_00_u03c1_49_);
v_e_59_ = lean_ctor_get(v___x_58_, 3);
lean_inc_ref(v_e_59_);
lean_dec_ref(v___x_58_);
v___x_60_ = lean_nat_sub(v_j_48_, v___x_50_);
v___x_61_ = lean_apply_1(v_e_59_, v___x_60_);
v___f_62_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_62_, 0, v___x_61_);
return v___f_62_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_wSz___boxed(lean_object* v_D_63_, lean_object* v_j_64_, lean_object* v_00_u03c1_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_BasicNotions_DV_wSz(v_D_63_, v_j_64_, v_00_u03c1_65_);
lean_dec(v_j_64_);
return v_res_66_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_srcPar___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_srcPar___closed__1(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_srcPar(lean_object* v_D_71_, lean_object* v_u_72_, lean_object* v_00_u03c4_73_, lean_object* v_i_74_){
_start:
{
lean_object* v_R_75_; lean_object* v_hcW_76_; lean_object* v_k_77_; lean_object* v_m_78_; lean_object* v_t_79_; uint8_t v___x_80_; 
v_R_75_ = lean_ctor_get(v_D_71_, 0);
lean_inc_ref(v_R_75_);
v_hcW_76_ = lean_ctor_get(v_D_71_, 9);
lean_inc_ref(v_hcW_76_);
lean_dec_ref(v_D_71_);
v_k_77_ = lean_ctor_get(v_R_75_, 1);
lean_inc(v_k_77_);
v_m_78_ = lean_ctor_get(v_R_75_, 2);
lean_inc(v_m_78_);
v_t_79_ = lean_ctor_get(v_R_75_, 3);
lean_inc(v_t_79_);
lean_dec_ref(v_R_75_);
v___x_80_ = lean_nat_dec_lt(v_i_74_, v_k_77_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_81_ = lean_nat_sub(v_i_74_, v_k_77_);
lean_dec(v_k_77_);
lean_dec(v_i_74_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_t_79_, v___x_82_);
v___x_84_ = lean_nat_div(v___x_81_, v___x_83_);
v___x_85_ = lean_nat_dec_lt(v___x_84_, v_m_78_);
lean_dec(v_m_78_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v___x_84_);
lean_dec(v___x_83_);
lean_dec(v___x_81_);
lean_dec(v_t_79_);
lean_dec_ref(v_hcW_76_);
lean_dec(v_00_u03c4_73_);
lean_dec(v_u_72_);
v___x_86_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_srcPar___closed__0, &lp_tree_Formalism_BasicNotions_DV_srcPar___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_srcPar___closed__0);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v_e_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_87_ = lean_apply_2(v_hcW_76_, v_u_72_, v_00_u03c4_73_);
v_e_88_ = lean_ctor_get(v___x_87_, 3);
lean_inc_ref(v_e_88_);
lean_dec_ref(v___x_87_);
v___x_89_ = lean_apply_1(v_e_88_, v___x_84_);
v___x_90_ = l_Rat_neg(v___x_89_);
v___x_91_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_79_);
v___x_92_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_srcPar___closed__1, &lp_tree_Formalism_BasicNotions_DV_srcPar___closed__1_once, _init_lp_tree_Formalism_BasicNotions_DV_srcPar___closed__1);
v___x_93_ = l_Rat_add(v___x_91_, v___x_92_);
v___x_94_ = lean_nat_mod(v___x_81_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_81_);
v___x_95_ = lean_nat_add(v___x_94_, v___x_82_);
lean_dec(v___x_94_);
v___x_96_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_95_);
v___x_97_ = l_Rat_mul(v___x_92_, v___x_96_);
v___x_98_ = l_Rat_sub(v___x_93_, v___x_97_);
v___x_99_ = l_Rat_div(v___x_98_, v___x_92_);
lean_dec_ref(v___x_98_);
v___x_100_ = l_Rat_add(v___x_90_, v___x_99_);
return v___x_100_;
}
}
else
{
lean_object* v___x_101_; lean_object* v_u_102_; lean_object* v___x_103_; 
lean_dec(v_t_79_);
lean_dec(v_m_78_);
lean_dec(v_k_77_);
v___x_101_ = lean_apply_2(v_hcW_76_, v_u_72_, v_00_u03c4_73_);
v_u_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_u_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = lean_apply_1(v_u_102_, v_i_74_);
return v___x_103_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
