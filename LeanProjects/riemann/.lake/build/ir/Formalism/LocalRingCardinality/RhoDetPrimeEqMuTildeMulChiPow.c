// Lean compiler output
// Module: Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.LocalRingCardinality.DataHost public import Formalism.LocalRingCardinality.DataSpaces public import Formalism.LocalRingCardinality.DataCoeff public import Formalism.LocalRingCardinality.DataArith public import Formalism.LocalRingCardinality.DataKernels public import Formalism.LocalRingCardinality.DataRows public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS public import Formalism.SharpRestriction.GrowthBounds.DataG public import Formalism.SharpRestriction.LevelLetterCocycles.DataN public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied public import Formalism.LocalRingCardinality.DataForms public import Formalism.LocalRingCardinality.DataJet public import Formalism.LocalRingCardinality.DataCD
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SDLat_smulLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SDLat_smulLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_D7_zmOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___redArg___lam__0(lean_object* v_x_1_, lean_object* v_inst_2_, lean_object* v_y_3_, lean_object* v_toMul_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc(v_i_5_);
v___x_6_ = lean_apply_1(v_x_1_, v_i_5_);
v___x_7_ = lean_apply_1(v_inst_2_, v___x_6_);
v___x_8_ = lean_apply_1(v_y_3_, v_i_5_);
v___x_9_ = lean_apply_2(v_toMul_4_, v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___redArg(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_N_12_, lean_object* v_x_13_, lean_object* v_y_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toSemiring_17_; lean_object* v_toAddCommMonoid_18_; lean_object* v___x_19_; lean_object* v_toMul_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v___x_15_ = lp_mathlib_Field_toSemifield___redArg(v_inst_10_);
v___x_16_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_15_);
v_toSemiring_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v___x_16_);
v_toAddCommMonoid_18_ = lean_ctor_get(v_toSemiring_17_, 0);
lean_inc_ref(v_toAddCommMonoid_18_);
v___x_19_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_17_);
v_toMul_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_toMul_20_);
lean_dec_ref(v___x_19_);
v___x_21_ = l_List_finRange(v_N_12_);
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_stdH___redArg___lam__0), 5, 4);
lean_closure_set(v___f_22_, 0, v_x_13_);
lean_closure_set(v___f_22_, 1, v_inst_11_);
lean_closure_set(v___f_22_, 2, v_y_14_);
lean_closure_set(v___f_22_, 3, v_toMul_20_);
v___x_23_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_18_, v___x_21_, v___f_22_);
lean_dec_ref(v_toAddCommMonoid_18_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___redArg___boxed(lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_N_26_, lean_object* v_x_27_, lean_object* v_y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_BasicNotions_stdH___redArg(v_inst_24_, v_inst_25_, v_N_26_, v_x_27_, v_y_28_);
lean_dec_ref(v_inst_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH(lean_object* v_E_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_N_33_, lean_object* v_x_34_, lean_object* v_y_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_BasicNotions_stdH___redArg(v_inst_31_, v_inst_32_, v_N_33_, v_x_34_, v_y_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_stdH___boxed(lean_object* v_E_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_N_40_, lean_object* v_x_41_, lean_object* v_y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_BasicNotions_stdH(v_E_37_, v_inst_38_, v_inst_39_, v_N_40_, v_x_41_, v_y_42_);
lean_dec_ref(v_inst_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SDLat_smulLat(lean_object* v_E_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_N_48_, lean_object* v_00_u03b3_49_, lean_object* v_L_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SDLat_smulLat___boxed(lean_object* v_E_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_N_56_, lean_object* v_00_u03b3_57_, lean_object* v_L_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_BasicNotions_SDLat_smulLat(v_E_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_N_56_, v_00_u03b3_57_, v_L_58_);
lean_dec(v_00_u03b3_57_);
lean_dec(v_N_56_);
lean_dec(v_inst_55_);
lean_dec_ref(v_inst_53_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_D7_zmOf(lean_object* v_D_60_, lean_object* v_u_61_){
_start:
{
lean_object* v_host_62_; lean_object* v_toHostAx_63_; lean_object* v_sp_64_; lean_object* v_cOf_65_; lean_object* v_instField_66_; lean_object* v___x_67_; lean_object* v_Y_68_; lean_object* v_zm_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_modE_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_toInv_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_host_62_ = lean_ctor_get(v_D_60_, 1);
v_toHostAx_63_ = lean_ctor_get(v_host_62_, 0);
lean_inc_ref(v_toHostAx_63_);
v_sp_64_ = lean_ctor_get(v_D_60_, 2);
lean_inc_ref(v_sp_64_);
v_cOf_65_ = lean_ctor_get(v_D_60_, 17);
lean_inc(v_cOf_65_);
lean_dec_ref(v_D_60_);
v_instField_66_ = lean_ctor_get(v_toHostAx_63_, 3);
lean_inc_ref(v_instField_66_);
lean_dec_ref(v_toHostAx_63_);
v___x_67_ = lp_mathlib_Field_toSemifield___redArg(v_instField_66_);
lean_dec_ref(v_instField_66_);
v_Y_68_ = lean_ctor_get(v_sp_64_, 5);
lean_inc_ref(v_Y_68_);
v_zm_69_ = lean_ctor_get(v_sp_64_, 8);
lean_inc(v_zm_69_);
lean_dec_ref(v_sp_64_);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_apply_1(v_Y_68_, v___x_70_);
v_modE_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_modE_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_67_);
lean_dec_ref(v___x_67_);
v___x_74_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_73_);
v___x_75_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_74_);
lean_dec_ref(v___x_74_);
v_toInv_76_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_toInv_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lean_apply_1(v_cOf_65_, v_u_61_);
v___x_78_ = lean_apply_1(v_toInv_76_, v___x_77_);
v___x_79_ = lean_apply_2(v_modE_72_, v___x_78_, v_zm_69_);
return v___x_79_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataHost(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataSpaces(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataCoeff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKernels(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataRows(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_DataS(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataN(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_AdicCompletionLocal_LocTied(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataJet(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataCD(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataHost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataSpaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataCoeff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKernels(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_DataS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_AdicCompletionLocal_LocTied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataJet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataCD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
