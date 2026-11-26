// Lean compiler output
// Module: Lib.DiscreteSeries.Theta.FockDualPair
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Rigidity.RepresentationsAndCasimirs public import Lib.GLn.SchurModule.Basic public import Lib.General.Algebra.MultivariatePolynomials public import Lib.Weil.Fock.Basic
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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Equiv_prodComm___redArg();
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_HCParam_lowestKType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairSign___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairSign___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairSign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairSign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_FockDualPair_std___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FockDualPair_std___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_FockDualPair_std___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FockDualPair_std___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_FockDualPair_std___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FockDualPair_std___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_FockDualPair_swap___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FockDualPair_swap___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_swap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_swap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_indexSign___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_indexSign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_FockDualPair_vacuumWeight___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_relWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_relWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_FockDualPair_centredParam___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FockDualPair_centredParam___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_pairSign___redArg(lean_object* v_00_u03c3_1_, lean_object* v_00_u03b5_2_, lean_object* v_00_u03b5_x27_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v_val_7_; lean_object* v_inv_8_; lean_object* v___x_9_; lean_object* v_val_10_; lean_object* v_inv_11_; lean_object* v___x_12_; lean_object* v_val_13_; lean_object* v_inv_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_25_; 
v_fst_5_ = lean_ctor_get(v_i_4_, 0);
lean_inc(v_fst_5_);
v_snd_6_ = lean_ctor_get(v_i_4_, 1);
lean_inc(v_snd_6_);
lean_dec_ref(v_i_4_);
v_val_7_ = lean_ctor_get(v_00_u03c3_1_, 0);
v_inv_8_ = lean_ctor_get(v_00_u03c3_1_, 1);
v___x_9_ = lean_apply_1(v_00_u03b5_2_, v_fst_5_);
v_val_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_val_10_);
v_inv_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_inv_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_apply_1(v_00_u03b5_x27_3_, v_snd_6_);
v_val_13_ = lean_ctor_get(v___x_12_, 0);
v_inv_14_ = lean_ctor_get(v___x_12_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_16_ = v___x_12_;
v_isShared_17_ = v_isSharedCheck_25_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_inv_14_);
lean_inc(v_val_13_);
lean_dec(v___x_12_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_25_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_18_ = lean_int_mul(v_val_7_, v_val_10_);
lean_dec(v_val_10_);
v___x_19_ = lean_int_mul(v_inv_11_, v_inv_8_);
lean_dec(v_inv_11_);
v___x_20_ = lean_int_mul(v___x_18_, v_val_13_);
lean_dec(v_val_13_);
lean_dec(v___x_18_);
v___x_21_ = lean_int_mul(v_inv_14_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v_inv_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 1, v___x_21_);
lean_ctor_set(v___x_16_, 0, v___x_20_);
v___x_23_ = v___x_16_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairSign___redArg___boxed(lean_object* v_00_u03c3_26_, lean_object* v_00_u03b5_27_, lean_object* v_00_u03b5_x27_28_, lean_object* v_i_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_pairSign___redArg(v_00_u03c3_26_, v_00_u03b5_27_, v_00_u03b5_x27_28_, v_i_29_);
lean_dec_ref(v_00_u03c3_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairSign(lean_object* v_R_31_, lean_object* v_C_32_, lean_object* v_00_u03c3_33_, lean_object* v_00_u03b5_34_, lean_object* v_00_u03b5_x27_35_, lean_object* v_i_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_GRH_New_pairSign___redArg(v_00_u03c3_33_, v_00_u03b5_34_, v_00_u03b5_x27_35_, v_i_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_pairSign___boxed(lean_object* v_R_38_, lean_object* v_C_39_, lean_object* v_00_u03c3_40_, lean_object* v_00_u03b5_41_, lean_object* v_00_u03b5_x27_42_, lean_object* v_i_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_pairSign(v_R_38_, v_C_39_, v_00_u03c3_40_, v_00_u03b5_41_, v_00_u03b5_x27_42_, v_i_43_);
lean_dec_ref(v_00_u03c3_40_);
return v_res_44_;
}
}
static lean_object* _init_lp_GRH_New_FockDualPair_std___redArg___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_lp_GRH_New_FockDualPair_std___redArg___closed__1(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_obj_once(&lp_GRH_New_FockDualPair_std___redArg___closed__0, &lp_GRH_New_FockDualPair_std___redArg___closed__0_once, _init_lp_GRH_New_FockDualPair_std___redArg___closed__0);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_FockDualPair_std___redArg___closed__2(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_mathlib_Equiv_refl___redArg();
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std___redArg(lean_object* v_inst_50_, lean_object* v_00_u03b3_51_, lean_object* v_00_u03b3_x27_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_53_ = lean_obj_once(&lp_GRH_New_FockDualPair_std___redArg___closed__1, &lp_GRH_New_FockDualPair_std___redArg___closed__1_once, _init_lp_GRH_New_FockDualPair_std___redArg___closed__1);
v___x_54_ = l_List_lengthTR___redArg(v_inst_50_);
v___x_55_ = lean_nat_to_int(v___x_54_);
v___x_56_ = lean_int_add(v_00_u03b3_x27_52_, v___x_55_);
lean_dec(v___x_55_);
v___x_57_ = lean_obj_once(&lp_GRH_New_FockDualPair_std___redArg___closed__2, &lp_GRH_New_FockDualPair_std___redArg___closed__2_once, _init_lp_GRH_New_FockDualPair_std___redArg___closed__2);
v___x_58_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_58_, 0, v___x_53_);
lean_ctor_set(v___x_58_, 1, v_00_u03b3_51_);
lean_ctor_set(v___x_58_, 2, v___x_56_);
lean_ctor_set(v___x_58_, 3, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std___redArg___boxed(lean_object* v_inst_59_, lean_object* v_00_u03b3_60_, lean_object* v_00_u03b3_x27_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_GRH_New_FockDualPair_std___redArg(v_inst_59_, v_00_u03b3_60_, v_00_u03b3_x27_61_);
lean_dec(v_00_u03b3_x27_61_);
lean_dec(v_inst_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std(lean_object* v_R_63_, lean_object* v_C_64_, lean_object* v_inst_65_, lean_object* v_00_u03b5_66_, lean_object* v_00_u03b5_x27_67_, lean_object* v_00_u03b3_68_, lean_object* v_00_u03b3_x27_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_70_ = lean_obj_once(&lp_GRH_New_FockDualPair_std___redArg___closed__1, &lp_GRH_New_FockDualPair_std___redArg___closed__1_once, _init_lp_GRH_New_FockDualPair_std___redArg___closed__1);
v___x_71_ = l_List_lengthTR___redArg(v_inst_65_);
v___x_72_ = lean_nat_to_int(v___x_71_);
v___x_73_ = lean_int_add(v_00_u03b3_x27_69_, v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_obj_once(&lp_GRH_New_FockDualPair_std___redArg___closed__2, &lp_GRH_New_FockDualPair_std___redArg___closed__2_once, _init_lp_GRH_New_FockDualPair_std___redArg___closed__2);
v___x_75_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
lean_ctor_set(v___x_75_, 1, v_00_u03b3_68_);
lean_ctor_set(v___x_75_, 2, v___x_73_);
lean_ctor_set(v___x_75_, 3, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_std___boxed(lean_object* v_R_76_, lean_object* v_C_77_, lean_object* v_inst_78_, lean_object* v_00_u03b5_79_, lean_object* v_00_u03b5_x27_80_, lean_object* v_00_u03b3_81_, lean_object* v_00_u03b3_x27_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_GRH_New_FockDualPair_std(v_R_76_, v_C_77_, v_inst_78_, v_00_u03b5_79_, v_00_u03b5_x27_80_, v_00_u03b3_81_, v_00_u03b3_x27_82_);
lean_dec(v_00_u03b3_x27_82_);
lean_dec_ref(v_00_u03b5_x27_80_);
lean_dec_ref(v_00_u03b5_79_);
lean_dec(v_inst_78_);
return v_res_83_;
}
}
static lean_object* _init_lp_GRH_New_FockDualPair_swap___redArg___closed__0(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_mathlib_Equiv_prodComm___redArg();
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_swap___redArg(lean_object* v_T_85_){
_start:
{
lean_object* v_globalSign_86_; lean_object* v_rowShift_87_; lean_object* v_columnShift_88_; lean_object* v_varEquiv_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_109_; 
v_globalSign_86_ = lean_ctor_get(v_T_85_, 0);
v_rowShift_87_ = lean_ctor_get(v_T_85_, 1);
v_columnShift_88_ = lean_ctor_get(v_T_85_, 2);
v_varEquiv_89_ = lean_ctor_get(v_T_85_, 3);
v_isSharedCheck_109_ = !lean_is_exclusive(v_T_85_);
if (v_isSharedCheck_109_ == 0)
{
v___x_91_ = v_T_85_;
v_isShared_92_ = v_isSharedCheck_109_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_varEquiv_89_);
lean_inc(v_columnShift_88_);
lean_inc(v_rowShift_87_);
lean_inc(v_globalSign_86_);
lean_dec(v_T_85_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_109_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_val_93_; lean_object* v_inv_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_108_; 
v_val_93_ = lean_ctor_get(v_globalSign_86_, 0);
v_inv_94_ = lean_ctor_get(v_globalSign_86_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_globalSign_86_);
if (v_isSharedCheck_108_ == 0)
{
v___x_96_ = v_globalSign_86_;
v_isShared_97_ = v_isSharedCheck_108_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_inv_94_);
lean_inc(v_val_93_);
lean_dec(v_globalSign_86_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_108_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_98_ = lean_int_neg(v_val_93_);
lean_dec(v_val_93_);
v___x_99_ = lean_int_neg(v_inv_94_);
lean_dec(v_inv_94_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_99_);
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_107_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_102_ = lean_obj_once(&lp_GRH_New_FockDualPair_swap___redArg___closed__0, &lp_GRH_New_FockDualPair_swap___redArg___closed__0_once, _init_lp_GRH_New_FockDualPair_swap___redArg___closed__0);
v___x_103_ = lp_mathlib_Equiv_trans___redArg(v___x_102_, v_varEquiv_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v___x_103_);
lean_ctor_set(v___x_91_, 2, v_rowShift_87_);
lean_ctor_set(v___x_91_, 1, v_columnShift_88_);
lean_ctor_set(v___x_91_, 0, v___x_101_);
v___x_105_ = v___x_91_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_columnShift_88_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_rowShift_87_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_swap(lean_object* v_R_110_, lean_object* v_C_111_, lean_object* v_00_u03b9_112_, lean_object* v_00_u03b5_113_, lean_object* v_00_u03b5_x27_114_, lean_object* v_T_115_){
_start:
{
lean_object* v_globalSign_116_; lean_object* v_rowShift_117_; lean_object* v_columnShift_118_; lean_object* v_varEquiv_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_139_; 
v_globalSign_116_ = lean_ctor_get(v_T_115_, 0);
v_rowShift_117_ = lean_ctor_get(v_T_115_, 1);
v_columnShift_118_ = lean_ctor_get(v_T_115_, 2);
v_varEquiv_119_ = lean_ctor_get(v_T_115_, 3);
v_isSharedCheck_139_ = !lean_is_exclusive(v_T_115_);
if (v_isSharedCheck_139_ == 0)
{
v___x_121_ = v_T_115_;
v_isShared_122_ = v_isSharedCheck_139_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_varEquiv_119_);
lean_inc(v_columnShift_118_);
lean_inc(v_rowShift_117_);
lean_inc(v_globalSign_116_);
lean_dec(v_T_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_139_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_val_123_; lean_object* v_inv_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_138_; 
v_val_123_ = lean_ctor_get(v_globalSign_116_, 0);
v_inv_124_ = lean_ctor_get(v_globalSign_116_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_globalSign_116_);
if (v_isSharedCheck_138_ == 0)
{
v___x_126_ = v_globalSign_116_;
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_inv_124_);
lean_inc(v_val_123_);
lean_dec(v_globalSign_116_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_int_neg(v_val_123_);
lean_dec(v_val_123_);
v___x_129_ = lean_int_neg(v_inv_124_);
lean_dec(v_inv_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_129_);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_131_ = v___x_126_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_137_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&lp_GRH_New_FockDualPair_swap___redArg___closed__0, &lp_GRH_New_FockDualPair_swap___redArg___closed__0_once, _init_lp_GRH_New_FockDualPair_swap___redArg___closed__0);
v___x_133_ = lp_mathlib_Equiv_trans___redArg(v___x_132_, v_varEquiv_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 3, v___x_133_);
lean_ctor_set(v___x_121_, 2, v_rowShift_117_);
lean_ctor_set(v___x_121_, 1, v_columnShift_118_);
lean_ctor_set(v___x_121_, 0, v___x_131_);
v___x_135_ = v___x_121_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_columnShift_118_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_rowShift_117_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_swap___boxed(lean_object* v_R_140_, lean_object* v_C_141_, lean_object* v_00_u03b9_142_, lean_object* v_00_u03b5_143_, lean_object* v_00_u03b5_x27_144_, lean_object* v_T_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_GRH_New_FockDualPair_swap(v_R_140_, v_C_141_, v_00_u03b9_142_, v_00_u03b5_143_, v_00_u03b5_x27_144_, v_T_145_);
lean_dec_ref(v_00_u03b5_x27_144_);
lean_dec_ref(v_00_u03b5_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign___redArg(lean_object* v_00_u03b5_147_, lean_object* v_00_u03b5_x27_148_, lean_object* v_T_149_, lean_object* v_i_150_){
_start:
{
lean_object* v_globalSign_151_; lean_object* v___x_152_; 
v_globalSign_151_ = lean_ctor_get(v_T_149_, 0);
v___x_152_ = lp_GRH_New_pairSign___redArg(v_globalSign_151_, v_00_u03b5_147_, v_00_u03b5_x27_148_, v_i_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign___redArg___boxed(lean_object* v_00_u03b5_153_, lean_object* v_00_u03b5_x27_154_, lean_object* v_T_155_, lean_object* v_i_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_GRH_New_FockDualPair_varSign___redArg(v_00_u03b5_153_, v_00_u03b5_x27_154_, v_T_155_, v_i_156_);
lean_dec_ref(v_T_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign(lean_object* v_R_158_, lean_object* v_C_159_, lean_object* v_00_u03b9_160_, lean_object* v_00_u03b5_161_, lean_object* v_00_u03b5_x27_162_, lean_object* v_T_163_, lean_object* v_i_164_){
_start:
{
lean_object* v_globalSign_165_; lean_object* v___x_166_; 
v_globalSign_165_ = lean_ctor_get(v_T_163_, 0);
v___x_166_ = lp_GRH_New_pairSign___redArg(v_globalSign_165_, v_00_u03b5_161_, v_00_u03b5_x27_162_, v_i_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_varSign___boxed(lean_object* v_R_167_, lean_object* v_C_168_, lean_object* v_00_u03b9_169_, lean_object* v_00_u03b5_170_, lean_object* v_00_u03b5_x27_171_, lean_object* v_T_172_, lean_object* v_i_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_GRH_New_FockDualPair_varSign(v_R_167_, v_C_168_, v_00_u03b9_169_, v_00_u03b5_170_, v_00_u03b5_x27_171_, v_T_172_, v_i_173_);
lean_dec_ref(v_T_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_indexSign___redArg(lean_object* v_00_u03b5_175_, lean_object* v_00_u03b5_x27_176_, lean_object* v_T_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_globalSign_179_; lean_object* v_varEquiv_180_; lean_object* v___x_181_; lean_object* v_toFun_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_globalSign_179_ = lean_ctor_get(v_T_177_, 0);
lean_inc_ref(v_globalSign_179_);
v_varEquiv_180_ = lean_ctor_get(v_T_177_, 3);
lean_inc_ref(v_varEquiv_180_);
lean_dec_ref(v_T_177_);
v___x_181_ = lp_mathlib_Equiv_symm___redArg(v_varEquiv_180_);
v_toFun_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_toFun_182_);
lean_dec_ref(v___x_181_);
v___x_183_ = lean_apply_1(v_toFun_182_, v_a_178_);
v___x_184_ = lp_GRH_New_pairSign___redArg(v_globalSign_179_, v_00_u03b5_175_, v_00_u03b5_x27_176_, v___x_183_);
lean_dec_ref(v_globalSign_179_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_indexSign(lean_object* v_R_185_, lean_object* v_C_186_, lean_object* v_00_u03b9_187_, lean_object* v_00_u03b5_188_, lean_object* v_00_u03b5_x27_189_, lean_object* v_T_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_globalSign_192_; lean_object* v_varEquiv_193_; lean_object* v___x_194_; lean_object* v_toFun_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_globalSign_192_ = lean_ctor_get(v_T_190_, 0);
lean_inc_ref(v_globalSign_192_);
v_varEquiv_193_ = lean_ctor_get(v_T_190_, 3);
lean_inc_ref(v_varEquiv_193_);
lean_dec_ref(v_T_190_);
v___x_194_ = lp_mathlib_Equiv_symm___redArg(v_varEquiv_193_);
v_toFun_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_toFun_195_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_apply_1(v_toFun_195_, v_a_191_);
v___x_197_ = lp_GRH_New_pairSign___redArg(v_globalSign_192_, v_00_u03b5_188_, v_00_u03b5_x27_189_, v___x_196_);
lean_dec_ref(v_globalSign_192_);
return v___x_197_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_FockDualPair_vacuumWeight___redArg___lam__0(lean_object* v_globalSign_198_, lean_object* v_s_199_, lean_object* v_00_u03b5_x27_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_val_202_; lean_object* v_inv_203_; lean_object* v_val_204_; lean_object* v_inv_205_; lean_object* v___x_206_; lean_object* v_val_207_; lean_object* v_inv_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_224_; 
v_val_202_ = lean_ctor_get(v_globalSign_198_, 0);
v_inv_203_ = lean_ctor_get(v_globalSign_198_, 1);
v_val_204_ = lean_ctor_get(v_s_199_, 0);
v_inv_205_ = lean_ctor_get(v_s_199_, 1);
v___x_206_ = lean_apply_1(v_00_u03b5_x27_200_, v_a_201_);
v_val_207_ = lean_ctor_get(v___x_206_, 0);
v_inv_208_ = lean_ctor_get(v___x_206_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_224_ == 0)
{
v___x_210_ = v___x_206_;
v_isShared_211_ = v_isSharedCheck_224_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_inv_208_);
lean_inc(v_val_207_);
lean_dec(v___x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_224_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_212_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_213_ = lean_int_mul(v_val_202_, v_val_204_);
v___x_214_ = lean_int_mul(v_inv_205_, v_inv_203_);
v___x_215_ = lean_int_mul(v___x_213_, v_val_207_);
lean_dec(v_val_207_);
lean_dec(v___x_213_);
v___x_216_ = lean_int_mul(v_inv_208_, v___x_214_);
lean_dec(v___x_214_);
lean_dec(v_inv_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_216_);
lean_ctor_set(v___x_210_, 0, v___x_215_);
v___x_218_ = v___x_210_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_223_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_obj_once(&lp_GRH_New_FockDualPair_std___redArg___closed__1, &lp_GRH_New_FockDualPair_std___redArg___closed__1_once, _init_lp_GRH_New_FockDualPair_std___redArg___closed__1);
v___x_220_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_212_, v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
v___x_221_ = 1;
return v___x_221_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight___redArg___lam__0___boxed(lean_object* v_globalSign_225_, lean_object* v_s_226_, lean_object* v_00_u03b5_x27_227_, lean_object* v_a_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = lp_GRH_New_FockDualPair_vacuumWeight___redArg___lam__0(v_globalSign_225_, v_s_226_, v_00_u03b5_x27_227_, v_a_228_);
lean_dec_ref(v_s_226_);
lean_dec_ref(v_globalSign_225_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight___redArg(lean_object* v_inst_231_, lean_object* v_00_u03b5_x27_232_, lean_object* v_T_233_, lean_object* v_s_234_){
_start:
{
lean_object* v_globalSign_235_; lean_object* v_rowShift_236_; lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_globalSign_235_ = lean_ctor_get(v_T_233_, 0);
lean_inc_ref(v_globalSign_235_);
v_rowShift_236_ = lean_ctor_get(v_T_233_, 1);
lean_inc(v_rowShift_236_);
lean_dec_ref(v_T_233_);
v___f_237_ = lean_alloc_closure((void*)(lp_GRH_New_FockDualPair_vacuumWeight___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_237_, 0, v_globalSign_235_);
lean_closure_set(v___f_237_, 1, v_s_234_);
lean_closure_set(v___f_237_, 2, v_00_u03b5_x27_232_);
v___x_238_ = lp_mathlib_Multiset_filter___redArg(v___f_237_, v_inst_231_);
v___x_239_ = l_List_lengthTR___redArg(v___x_238_);
lean_dec(v___x_238_);
v___x_240_ = lean_nat_to_int(v___x_239_);
v___x_241_ = lean_int_sub(v_rowShift_236_, v___x_240_);
lean_dec(v___x_240_);
lean_dec(v_rowShift_236_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight(lean_object* v_R_242_, lean_object* v_C_243_, lean_object* v_00_u03b9_244_, lean_object* v_inst_245_, lean_object* v_00_u03b5_246_, lean_object* v_00_u03b5_x27_247_, lean_object* v_T_248_, lean_object* v_s_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lp_GRH_New_FockDualPair_vacuumWeight___redArg(v_inst_245_, v_00_u03b5_x27_247_, v_T_248_, v_s_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_vacuumWeight___boxed(lean_object* v_R_251_, lean_object* v_C_252_, lean_object* v_00_u03b9_253_, lean_object* v_inst_254_, lean_object* v_00_u03b5_255_, lean_object* v_00_u03b5_x27_256_, lean_object* v_T_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = lp_GRH_New_FockDualPair_vacuumWeight(v_R_251_, v_C_252_, v_00_u03b9_253_, v_inst_254_, v_00_u03b5_255_, v_00_u03b5_x27_256_, v_T_257_, v_s_258_);
lean_dec_ref(v_00_u03b5_255_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_relWeight___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_00_u03b5_262_, lean_object* v_00_u03b5_x27_263_, lean_object* v_T_264_, lean_object* v_l_265_, lean_object* v_r_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc(v_r_266_);
lean_inc_ref(v_00_u03b5_262_);
v___x_267_ = lp_GRH_New_HCParam_lowestKType___redArg(v_inst_261_, v_00_u03b5_262_, v_l_265_, v_r_266_);
v___x_268_ = lean_apply_1(v_00_u03b5_262_, v_r_266_);
v___x_269_ = lp_GRH_New_FockDualPair_vacuumWeight___redArg(v_inst_260_, v_00_u03b5_x27_263_, v_T_264_, v___x_268_);
v___x_270_ = lean_int_sub(v___x_267_, v___x_269_);
lean_dec(v___x_269_);
lean_dec(v___x_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_relWeight(lean_object* v_R_271_, lean_object* v_C_272_, lean_object* v_00_u03b9_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_00_u03b5_276_, lean_object* v_00_u03b5_x27_277_, lean_object* v_T_278_, lean_object* v_l_279_, lean_object* v_r_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc(v_r_280_);
lean_inc_ref(v_00_u03b5_276_);
v___x_281_ = lp_GRH_New_HCParam_lowestKType___redArg(v_inst_275_, v_00_u03b5_276_, v_l_279_, v_r_280_);
v___x_282_ = lean_apply_1(v_00_u03b5_276_, v_r_280_);
v___x_283_ = lp_GRH_New_FockDualPair_vacuumWeight___redArg(v_inst_274_, v_00_u03b5_x27_277_, v_T_278_, v___x_282_);
v___x_284_ = lean_int_sub(v___x_281_, v___x_283_);
lean_dec(v___x_283_);
lean_dec(v___x_281_);
return v___x_284_;
}
}
static lean_object* _init_lp_GRH_New_FockDualPair_centredParam___redArg___closed__0(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(2u);
v___x_286_ = lean_nat_to_int(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam___redArg(lean_object* v_inst_287_, lean_object* v_T_288_, lean_object* v_l_289_, lean_object* v_r_290_){
_start:
{
lean_object* v_rowShift_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_rowShift_291_ = lean_ctor_get(v_T_288_, 1);
v___x_292_ = lean_apply_1(v_l_289_, v_r_290_);
v___x_293_ = lean_obj_once(&lp_GRH_New_FockDualPair_centredParam___redArg___closed__0, &lp_GRH_New_FockDualPair_centredParam___redArg___closed__0_once, _init_lp_GRH_New_FockDualPair_centredParam___redArg___closed__0);
v___x_294_ = lean_int_mul(v___x_293_, v_rowShift_291_);
v___x_295_ = lean_int_sub(v___x_292_, v___x_294_);
lean_dec(v___x_294_);
lean_dec(v___x_292_);
v___x_296_ = l_List_lengthTR___redArg(v_inst_287_);
v___x_297_ = lean_nat_to_int(v___x_296_);
v___x_298_ = lean_int_add(v___x_295_, v___x_297_);
lean_dec(v___x_297_);
lean_dec(v___x_295_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam___redArg___boxed(lean_object* v_inst_299_, lean_object* v_T_300_, lean_object* v_l_301_, lean_object* v_r_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = lp_GRH_New_FockDualPair_centredParam___redArg(v_inst_299_, v_T_300_, v_l_301_, v_r_302_);
lean_dec_ref(v_T_300_);
lean_dec(v_inst_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam(lean_object* v_R_304_, lean_object* v_C_305_, lean_object* v_00_u03b9_306_, lean_object* v_inst_307_, lean_object* v_00_u03b5_308_, lean_object* v_00_u03b5_x27_309_, lean_object* v_T_310_, lean_object* v_l_311_, lean_object* v_r_312_){
_start:
{
lean_object* v_rowShift_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_rowShift_313_ = lean_ctor_get(v_T_310_, 1);
v___x_314_ = lean_apply_1(v_l_311_, v_r_312_);
v___x_315_ = lean_obj_once(&lp_GRH_New_FockDualPair_centredParam___redArg___closed__0, &lp_GRH_New_FockDualPair_centredParam___redArg___closed__0_once, _init_lp_GRH_New_FockDualPair_centredParam___redArg___closed__0);
v___x_316_ = lean_int_mul(v___x_315_, v_rowShift_313_);
v___x_317_ = lean_int_sub(v___x_314_, v___x_316_);
lean_dec(v___x_316_);
lean_dec(v___x_314_);
v___x_318_ = l_List_lengthTR___redArg(v_inst_307_);
v___x_319_ = lean_nat_to_int(v___x_318_);
v___x_320_ = lean_int_add(v___x_317_, v___x_319_);
lean_dec(v___x_319_);
lean_dec(v___x_317_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_centredParam___boxed(lean_object* v_R_321_, lean_object* v_C_322_, lean_object* v_00_u03b9_323_, lean_object* v_inst_324_, lean_object* v_00_u03b5_325_, lean_object* v_00_u03b5_x27_326_, lean_object* v_T_327_, lean_object* v_l_328_, lean_object* v_r_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = lp_GRH_New_FockDualPair_centredParam(v_R_321_, v_C_322_, v_00_u03b9_323_, v_inst_324_, v_00_u03b5_325_, v_00_u03b5_x27_326_, v_T_327_, v_l_328_, v_r_329_);
lean_dec_ref(v_T_327_);
lean_dec_ref(v_00_u03b5_x27_326_);
lean_dec_ref(v_00_u03b5_325_);
lean_dec(v_inst_324_);
return v_res_330_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Rigidity_RepresentationsAndCasimirs(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Fock_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_FockDualPair(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Rigidity_RepresentationsAndCasimirs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_SchurModule_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Fock_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
