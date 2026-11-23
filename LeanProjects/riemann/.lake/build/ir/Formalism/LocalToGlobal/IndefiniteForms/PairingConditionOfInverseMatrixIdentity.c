// Lean compiler output
// Module: Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
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
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCols_toR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCols_toR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCols_toR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCore_toR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCore_toR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCore_toR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___redArg___lam__0(lean_object* v_00_u03b6_1_, lean_object* v_toInv_2_, lean_object* v_u_3_, lean_object* v_t_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_2(v_00_u03b6_1_, v_u_3_, v_t_4_);
v___x_6_ = lean_apply_1(v_toInv_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___redArg(lean_object* v_inst_7_, lean_object* v_C_8_){
_start:
{
lean_object* v_B_9_; lean_object* v_00_u03b6_10_; lean_object* v_sE_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_24_; 
v_B_9_ = lean_ctor_get(v_C_8_, 0);
v_00_u03b6_10_ = lean_ctor_get(v_C_8_, 1);
v_sE_11_ = lean_ctor_get(v_C_8_, 2);
v_isSharedCheck_24_ = !lean_is_exclusive(v_C_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_13_ = v_C_8_;
v_isShared_14_ = v_isSharedCheck_24_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_sE_11_);
lean_inc(v_00_u03b6_10_);
lean_inc(v_B_9_);
lean_dec(v_C_8_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_24_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toInv_19_; lean_object* v___f_20_; lean_object* v___x_22_; 
v___x_15_ = lp_mathlib_Field_toSemifield___redArg(v_inst_7_);
v___x_16_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_15_);
lean_dec_ref(v___x_15_);
v___x_17_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_16_);
v___x_18_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_17_);
lean_dec_ref(v___x_17_);
v_toInv_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_toInv_19_);
lean_dec_ref(v___x_18_);
v___f_20_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Indef_ColData_invZ___redArg___lam__0), 4, 2);
lean_closure_set(v___f_20_, 0, v_00_u03b6_10_);
lean_closure_set(v___f_20_, 1, v_toInv_19_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___f_20_);
v___x_22_ = v___x_13_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_B_9_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___f_20_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_sE_11_);
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___redArg___boxed(lean_object* v_inst_25_, lean_object* v_C_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_L2_Indef_ColData_invZ___redArg(v_inst_25_, v_C_26_);
lean_dec_ref(v_inst_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ(lean_object* v_K_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_Bs_32_, lean_object* v_Df_33_, lean_object* v_Dc_34_, lean_object* v_Sp_35_, lean_object* v_S_36_, lean_object* v_C_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_tree_Formalism_L2_Indef_ColData_invZ___redArg(v_inst_29_, v_C_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_ColData_invZ___boxed(lean_object* v_K_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_Bs_43_, lean_object* v_Df_44_, lean_object* v_Dc_45_, lean_object* v_Sp_46_, lean_object* v_S_47_, lean_object* v_C_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_L2_Indef_ColData_invZ(v_K_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_Bs_43_, v_Df_44_, v_Dc_45_, v_Sp_46_, v_S_47_, v_C_48_);
lean_dec_ref(v_S_47_);
lean_dec_ref(v_Sp_46_);
lean_dec_ref(v_Dc_45_);
lean_dec_ref(v_Df_44_);
lean_dec_ref(v_Bs_43_);
lean_dec(v_inst_42_);
lean_dec_ref(v_inst_40_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget___redArg(lean_object* v_P_50_){
_start:
{
lean_object* v_toIndefPkg_51_; 
v_toIndefPkg_51_ = lean_ctor_get(v_P_50_, 0);
lean_inc_ref(v_toIndefPkg_51_);
return v_toIndefPkg_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget___redArg___boxed(lean_object* v_P_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_L2_Indef_IndefPkg2_forget___redArg(v_P_52_);
lean_dec_ref(v_P_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget(lean_object* v_K_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_Bs_58_, lean_object* v_A_59_, lean_object* v_fc_60_, lean_object* v_cf_61_, lean_object* v_C_62_, lean_object* v_CH_63_, lean_object* v_P_64_){
_start:
{
lean_object* v_toIndefPkg_65_; 
v_toIndefPkg_65_ = lean_ctor_get(v_P_64_, 0);
lean_inc_ref(v_toIndefPkg_65_);
return v_toIndefPkg_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefPkg2_forget___boxed(lean_object* v_K_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_Bs_70_, lean_object* v_A_71_, lean_object* v_fc_72_, lean_object* v_cf_73_, lean_object* v_C_74_, lean_object* v_CH_75_, lean_object* v_P_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_L2_Indef_IndefPkg2_forget(v_K_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_Bs_70_, v_A_71_, v_fc_72_, v_cf_73_, v_C_74_, v_CH_75_, v_P_76_);
lean_dec_ref(v_P_76_);
lean_dec(v_CH_75_);
lean_dec(v_C_74_);
lean_dec_ref(v_cf_73_);
lean_dec_ref(v_fc_72_);
lean_dec_ref(v_A_71_);
lean_dec_ref(v_Bs_70_);
lean_dec(v_inst_69_);
lean_dec_ref(v_inst_67_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCols_toR___redArg(lean_object* v_S_78_){
_start:
{
lean_object* v_toIndefRows_79_; lean_object* v_col_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_toIndefRows_79_ = lean_ctor_get(v_S_78_, 0);
v_col_80_ = lean_ctor_get(v_S_78_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_S_78_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v_S_78_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_col_80_);
lean_inc(v_toIndefRows_79_);
lean_dec(v_S_78_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_toIndefRows_79_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_col_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCols_toR(lean_object* v_K_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_Bs_92_, lean_object* v_Df_93_, lean_object* v_Dc_94_, lean_object* v_Sp_95_, lean_object* v_N_96_, lean_object* v_S_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_tree_Formalism_L2_Indef_IndefCols_toR___redArg(v_S_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCols_toR___boxed(lean_object* v_K_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_Bs_103_, lean_object* v_Df_104_, lean_object* v_Dc_105_, lean_object* v_Sp_106_, lean_object* v_N_107_, lean_object* v_S_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Formalism_L2_Indef_IndefCols_toR(v_K_99_, v_inst_100_, v_inst_101_, v_inst_102_, v_Bs_103_, v_Df_104_, v_Dc_105_, v_Sp_106_, v_N_107_, v_S_108_);
lean_dec_ref(v_N_107_);
lean_dec_ref(v_Sp_106_);
lean_dec_ref(v_Dc_105_);
lean_dec_ref(v_Df_104_);
lean_dec_ref(v_Bs_103_);
lean_dec(v_inst_102_);
lean_dec_ref(v_inst_100_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCore_toR___redArg(lean_object* v_P_110_){
_start:
{
lean_object* v_base_111_; lean_object* v_cols_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
v_base_111_ = lean_ctor_get(v_P_110_, 0);
v_cols_112_ = lean_ctor_get(v_P_110_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_P_110_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v_P_110_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_cols_112_);
lean_inc(v_base_111_);
lean_dec(v_P_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lp_tree_Formalism_L2_Indef_IndefCols_toR___redArg(v_cols_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_base_111_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCore_toR(lean_object* v_K_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_Bs_125_, lean_object* v_Df0_126_, lean_object* v_Df1_127_, lean_object* v_Dc_128_, lean_object* v_Sp_129_, lean_object* v_N_130_, lean_object* v_P_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_tree_Formalism_L2_Indef_IndefCore_toR___redArg(v_P_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Indef_IndefCore_toR___boxed(lean_object* v_K_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_Bs_137_, lean_object* v_Df0_138_, lean_object* v_Df1_139_, lean_object* v_Dc_140_, lean_object* v_Sp_141_, lean_object* v_N_142_, lean_object* v_P_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_tree_Formalism_L2_Indef_IndefCore_toR(v_K_133_, v_inst_134_, v_inst_135_, v_inst_136_, v_Bs_137_, v_Df0_138_, v_Df1_139_, v_Dc_140_, v_Sp_141_, v_N_142_, v_P_143_);
lean_dec_ref(v_N_142_);
lean_dec_ref(v_Sp_141_);
lean_dec_ref(v_Dc_140_);
lean_dec_ref(v_Df1_139_);
lean_dec_ref(v_Df0_138_);
lean_dec_ref(v_Bs_137_);
lean_dec(v_inst_136_);
lean_dec_ref(v_inst_134_);
return v_res_144_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefSide(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefUse(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefSide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefUse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
