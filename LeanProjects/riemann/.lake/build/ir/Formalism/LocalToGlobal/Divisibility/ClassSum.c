// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.ClassSum
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.RatHermLcvTwist public import Formalism.QuotientMetricDivisors.ClassSumDualGeF
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
extern lean_object* lp_mathlib_Nat_instCommMonoidWithZero;
extern lean_object* lp_mathlib_instStrongNormalizedGCDMonoidNat;
lean_object* lp_mathlib_instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Finset_lcm___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_Forms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_Forms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_wt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_wt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_wt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_CSD_DGam___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_CSD_DGam___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_DGam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_DGam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_Forms(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_S_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_Forms___boxed(lean_object* v_K_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_S_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_DIV_CSD_Forms(v_K_7_, v_inst_8_, v_inst_9_, v_inst_10_, v_S_11_);
lean_dec_ref(v_S_11_);
lean_dec(v_inst_10_);
lean_dec_ref(v_inst_8_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_wt___redArg(lean_object* v_S_13_, lean_object* v_c_14_){
_start:
{
lean_object* v_finGam_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_finGam_15_ = lean_ctor_get(v_S_13_, 9);
lean_inc(v_finGam_15_);
lean_dec_ref(v_S_13_);
v___x_16_ = lean_apply_1(v_finGam_15_, v_c_14_);
v___x_17_ = l_List_lengthTR___redArg(v___x_16_);
lean_dec(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_wt(lean_object* v_K_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_S_22_, lean_object* v_c_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_tree_Formalism_L2_DIV_CSD_wt___redArg(v_S_22_, v_c_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_wt___boxed(lean_object* v_K_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_S_29_, lean_object* v_c_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_L2_DIV_CSD_wt(v_K_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_S_29_, v_c_30_);
lean_dec(v_inst_28_);
lean_dec_ref(v_inst_26_);
return v_res_31_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_CSD_DGam___redArg___closed__0(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lp_mathlib_instStrongNormalizedGCDMonoidNat;
v___x_33_ = lp_mathlib_instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid___redArg(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_DGam___redArg(lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_S_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v_finCl_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_37_ = lp_mathlib_Nat_instCommMonoidWithZero;
v___x_38_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_CSD_DGam___redArg___closed__0, &lp_tree_Formalism_L2_DIV_CSD_DGam___redArg___closed__0_once, _init_lp_tree_Formalism_L2_DIV_CSD_DGam___redArg___closed__0);
v_finCl_39_ = lean_ctor_get(v_S_36_, 0);
lean_inc(v_finCl_39_);
v___x_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_CSD_wt___boxed), 6, 5);
lean_closure_set(v___x_40_, 0, lean_box(0));
lean_closure_set(v___x_40_, 1, v_inst_34_);
lean_closure_set(v___x_40_, 2, lean_box(0));
lean_closure_set(v___x_40_, 3, v_inst_35_);
lean_closure_set(v___x_40_, 4, v_S_36_);
v___x_41_ = lp_mathlib_Finset_lcm___redArg(v___x_37_, v___x_38_, v_finCl_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_DGam(lean_object* v_K_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_S_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_L2_DIV_CSD_DGam___redArg(v_inst_43_, v_inst_45_, v_S_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum___redArg___lam__0(lean_object* v_S_48_, lean_object* v_toNatCast_49_, lean_object* v_toInv_50_, lean_object* v_f_51_, lean_object* v_g_52_, lean_object* v_pair_53_, lean_object* v_toMul_54_, lean_object* v_c_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
lean_inc_n(v_c_55_, 2);
v___x_56_ = lp_tree_Formalism_L2_DIV_CSD_wt___redArg(v_S_48_, v_c_55_);
v___x_57_ = lean_apply_1(v_toNatCast_49_, v___x_56_);
v___x_58_ = lean_apply_1(v_toInv_50_, v___x_57_);
v___x_59_ = lean_apply_1(v_f_51_, v_c_55_);
v___x_60_ = lean_apply_1(v_g_52_, v_c_55_);
v___x_61_ = lean_apply_2(v_pair_53_, v___x_59_, v___x_60_);
v___x_62_ = lean_apply_2(v_toMul_54_, v___x_58_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum___redArg(lean_object* v_inst_63_, lean_object* v_S_64_, lean_object* v_f_65_, lean_object* v_g_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toSemiring_69_; lean_object* v_toAddCommMonoid_70_; lean_object* v_finCl_71_; lean_object* v_pair_72_; lean_object* v___x_73_; lean_object* v_toMul_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_toInv_78_; lean_object* v___x_79_; lean_object* v_toRing_80_; lean_object* v___x_81_; lean_object* v_toAddMonoidWithOne_82_; lean_object* v_toNatCast_83_; lean_object* v___f_84_; lean_object* v___x_85_; 
v___x_67_ = lp_mathlib_Field_toSemifield___redArg(v_inst_63_);
lean_inc_ref(v___x_67_);
v___x_68_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_67_);
v_toSemiring_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_toSemiring_69_);
lean_dec_ref(v___x_68_);
v_toAddCommMonoid_70_ = lean_ctor_get(v_toSemiring_69_, 0);
lean_inc_ref(v_toAddCommMonoid_70_);
v_finCl_71_ = lean_ctor_get(v_S_64_, 0);
lean_inc(v_finCl_71_);
v_pair_72_ = lean_ctor_get(v_S_64_, 7);
lean_inc(v_pair_72_);
v___x_73_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_69_);
v_toMul_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_toMul_74_);
lean_dec_ref(v___x_73_);
v___x_75_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_67_);
lean_dec_ref(v___x_67_);
v___x_76_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_75_);
v___x_77_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_76_);
lean_dec_ref(v___x_76_);
v_toInv_78_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_toInv_78_);
lean_dec_ref(v___x_77_);
v___x_79_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_63_);
v_toRing_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_toRing_80_);
lean_dec_ref(v___x_79_);
v___x_81_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_80_);
v_toAddMonoidWithOne_82_ = lean_ctor_get(v___x_81_, 1);
lean_inc_ref(v_toAddMonoidWithOne_82_);
lean_dec_ref(v___x_81_);
v_toNatCast_83_ = lean_ctor_get(v_toAddMonoidWithOne_82_, 0);
lean_inc(v_toNatCast_83_);
lean_dec_ref(v_toAddMonoidWithOne_82_);
v___f_84_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_CSD_csum___redArg___lam__0), 8, 7);
lean_closure_set(v___f_84_, 0, v_S_64_);
lean_closure_set(v___f_84_, 1, v_toNatCast_83_);
lean_closure_set(v___f_84_, 2, v_toInv_78_);
lean_closure_set(v___f_84_, 3, v_f_65_);
lean_closure_set(v___f_84_, 4, v_g_66_);
lean_closure_set(v___f_84_, 5, v_pair_72_);
lean_closure_set(v___f_84_, 6, v_toMul_74_);
v___x_85_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_70_, v_finCl_71_, v___f_84_);
lean_dec_ref(v_toAddCommMonoid_70_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum(lean_object* v_K_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_S_90_, lean_object* v_f_91_, lean_object* v_g_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_tree_Formalism_L2_DIV_CSD_csum___redArg(v_inst_87_, v_S_90_, v_f_91_, v_g_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_csum___boxed(lean_object* v_K_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_S_98_, lean_object* v_f_99_, lean_object* v_g_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Formalism_L2_DIV_CSD_csum(v_K_94_, v_inst_95_, v_inst_96_, v_inst_97_, v_S_98_, v_f_99_, v_g_100_);
lean_dec(v_inst_97_);
return v_res_101_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualGeF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ClassSum(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualGeF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
