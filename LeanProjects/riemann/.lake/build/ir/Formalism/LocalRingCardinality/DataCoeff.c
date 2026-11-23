// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataCoeff
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.GradedWeylDivisibility.StatementA public import Formalism.GradedWeylDivisibility.StatementB public import Formalism.SatakeDualWeyl.StatementW
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_det___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_natW(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_natW___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_dual___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_dual___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_dual(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_spread(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_rhoVec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_rhoVec___closed__0;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_rhoVec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_rhoVec___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_rhoVec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_hcToWeightQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_inside_u2082___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_inside_u2082(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_inside_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift(lean_object* v_N_3_, lean_object* v_lam_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_dec_lt(v___x_5_, v_N_3_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec_ref(v_lam_4_);
v___x_7_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0, &lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0);
return v___x_7_;
}
else
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_sub(v_N_3_, v___x_8_);
v___x_10_ = lean_apply_1(v_lam_4_, v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift___boxed(lean_object* v_N_11_, lean_object* v_lam_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v_N_11_, v_lam_12_);
lean_dec(v_N_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_natW(lean_object* v_N_14_, lean_object* v_lam_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc_ref(v_lam_15_);
v___x_17_ = lean_apply_1(v_lam_15_, v_i_16_);
v___x_18_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v_N_14_, v_lam_15_);
v___x_19_ = lean_int_sub(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_17_);
v___x_20_ = l_Int_toNat(v___x_19_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_natW___boxed(lean_object* v_N_21_, lean_object* v_lam_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_BasicNotions_DomWeight_natW(v_N_21_, v_lam_22_, v_i_23_);
lean_dec(v_N_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_dual___lam__0(lean_object* v_N_25_, lean_object* v_lam_26_, lean_object* v_i_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_add(v_i_27_, v___x_28_);
v___x_30_ = lean_nat_sub(v_N_25_, v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = lean_apply_1(v_lam_26_, v___x_30_);
v___x_32_ = lean_int_neg(v___x_31_);
lean_dec(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_dual___lam__0___boxed(lean_object* v_N_33_, lean_object* v_lam_34_, lean_object* v_i_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_BasicNotions_DomWeight_dual___lam__0(v_N_33_, v_lam_34_, v_i_35_);
lean_dec(v_i_35_);
lean_dec(v_N_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_dual(lean_object* v_N_37_, lean_object* v_lam_38_){
_start:
{
lean_object* v___f_39_; 
v___f_39_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_DomWeight_dual___lam__0___boxed), 3, 2);
lean_closure_set(v___f_39_, 0, v_N_37_);
lean_closure_set(v___f_39_, 1, v_lam_38_);
return v___f_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DomWeight_spread(lean_object* v_N_40_, lean_object* v_lam_41_){
_start:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_nat_dec_lt(v___x_42_, v_N_40_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
lean_dec_ref(v_lam_41_);
lean_dec(v_N_40_);
v___x_44_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0, &lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0);
return v___x_44_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
lean_inc_ref(v_lam_41_);
v___x_45_ = lean_apply_1(v_lam_41_, v___x_42_);
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_sub(v_N_40_, v___x_46_);
v___x_48_ = lean_apply_1(v_lam_41_, v___x_47_);
v___x_49_ = lean_int_sub(v___x_45_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_45_);
v___x_50_ = lean_nat_to_int(v_N_40_);
v___x_51_ = lean_int_add(v___x_49_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v___x_49_);
return v___x_51_;
}
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_rhoVec___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_rhoVec___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(2u);
v___x_55_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_rhoVec(lean_object* v_N_56_, lean_object* v_i_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_58_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_N_56_);
v___x_59_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_rhoVec___closed__0, &lp_tree_Formalism_BasicNotions_rhoVec___closed__0_once, _init_lp_tree_Formalism_BasicNotions_rhoVec___closed__0);
v___x_60_ = l_Rat_sub(v___x_58_, v___x_59_);
v___x_61_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_rhoVec___closed__1, &lp_tree_Formalism_BasicNotions_rhoVec___closed__1_once, _init_lp_tree_Formalism_BasicNotions_rhoVec___closed__1);
v___x_62_ = l_Rat_div(v___x_60_, v___x_61_);
lean_dec_ref(v___x_60_);
v___x_63_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_57_);
v___x_64_ = l_Rat_sub(v___x_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_hcToWeightQ(lean_object* v_N_65_, lean_object* v_hc_66_, lean_object* v_i_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_inc(v_i_67_);
v___x_68_ = lean_apply_1(v_hc_66_, v_i_67_);
v___x_69_ = lp_tree_Formalism_BasicNotions_rhoVec(v_N_65_, v_i_67_);
v___x_70_ = l_Rat_sub(v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow___redArg(lean_object* v_inst_71_, lean_object* v_N_72_, lean_object* v_g_73_, lean_object* v_c_74_){
_start:
{
lean_object* v_toSemiring_75_; lean_object* v_toMonoid_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v_intZero_80_; uint8_t v_isNeg_81_; 
v_toSemiring_75_ = lean_ctor_get(v_inst_71_, 0);
v_toMonoid_76_ = lean_ctor_get(v_toSemiring_75_, 1);
lean_inc_ref(v_toMonoid_76_);
lean_inc(v_N_72_);
v___x_77_ = l_List_finRange(v_N_72_);
v___x_78_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_78_, 0, v_N_72_);
v___x_79_ = lp_mathlib_Matrix_GeneralLinearGroup_det___redArg___lam__0(v___x_78_, v___x_77_, v_inst_71_, v_g_73_);
v_intZero_80_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0, &lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DomWeight_detShift___closed__0);
v_isNeg_81_ = lean_int_dec_lt(v_c_74_, v_intZero_80_);
if (v_isNeg_81_ == 0)
{
lean_object* v_toNPow_82_; lean_object* v_val_83_; lean_object* v_a_84_; lean_object* v___x_85_; 
v_toNPow_82_ = lean_ctor_get(v_toMonoid_76_, 2);
lean_inc(v_toNPow_82_);
lean_dec_ref(v_toMonoid_76_);
v_val_83_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_83_);
lean_dec_ref(v___x_79_);
v_a_84_ = lean_nat_abs(v_c_74_);
v___x_85_ = lean_apply_2(v_toNPow_82_, v_a_84_, v_val_83_);
return v___x_85_;
}
else
{
lean_object* v_toNPow_86_; lean_object* v_inv_87_; lean_object* v_abs_88_; lean_object* v_one_89_; lean_object* v_a_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_toNPow_86_ = lean_ctor_get(v_toMonoid_76_, 2);
lean_inc(v_toNPow_86_);
lean_dec_ref(v_toMonoid_76_);
v_inv_87_ = lean_ctor_get(v___x_79_, 1);
lean_inc(v_inv_87_);
lean_dec_ref(v___x_79_);
v_abs_88_ = lean_nat_abs(v_c_74_);
v_one_89_ = lean_unsigned_to_nat(1u);
v_a_90_ = lean_nat_sub(v_abs_88_, v_one_89_);
lean_dec(v_abs_88_);
v___x_91_ = lean_nat_add(v_a_90_, v_one_89_);
lean_dec(v_a_90_);
v___x_92_ = lean_apply_2(v_toNPow_86_, v___x_91_, v_inv_87_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow___redArg___boxed(lean_object* v_inst_93_, lean_object* v_N_94_, lean_object* v_g_95_, lean_object* v_c_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_Formalism_BasicNotions_detPow___redArg(v_inst_93_, v_N_94_, v_g_95_, v_c_96_);
lean_dec(v_c_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow(lean_object* v_R_98_, lean_object* v_inst_99_, lean_object* v_N_100_, lean_object* v_g_101_, lean_object* v_c_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_tree_Formalism_BasicNotions_detPow___redArg(v_inst_99_, v_N_100_, v_g_101_, v_c_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_detPow___boxed(lean_object* v_R_104_, lean_object* v_inst_105_, lean_object* v_N_106_, lean_object* v_g_107_, lean_object* v_c_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Formalism_BasicNotions_detPow(v_R_104_, v_inst_105_, v_N_106_, v_g_107_, v_c_108_);
lean_dec(v_c_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_inside_u2082___redArg(lean_object* v_g_110_){
_start:
{
lean_object* v_val_111_; lean_object* v_inv_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_121_; 
v_val_111_ = lean_ctor_get(v_g_110_, 0);
v_inv_112_ = lean_ctor_get(v_g_110_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_g_110_);
if (v_isSharedCheck_121_ == 0)
{
v___x_114_ = v_g_110_;
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_inv_112_);
lean_inc(v_val_111_);
lean_dec(v_g_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, lean_box(0));
lean_closure_set(v___x_116_, 2, lean_box(0));
lean_closure_set(v___x_116_, 3, v_inv_112_);
v___x_117_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_117_, 0, lean_box(0));
lean_closure_set(v___x_117_, 1, lean_box(0));
lean_closure_set(v___x_117_, 2, lean_box(0));
lean_closure_set(v___x_117_, 3, v_val_111_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_117_);
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_inside_u2082(lean_object* v_R_122_, lean_object* v_inst_123_, lean_object* v_N_124_, lean_object* v_g_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_tree_Formalism_BasicNotions_inside_u2082___redArg(v_g_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_inside_u2082___boxed(lean_object* v_R_127_, lean_object* v_inst_128_, lean_object* v_N_129_, lean_object* v_g_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Formalism_BasicNotions_inside_u2082(v_R_127_, v_inst_128_, v_N_129_, v_g_130_);
lean_dec(v_N_129_);
lean_dec_ref(v_inst_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg___lam__0(lean_object* v_t_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_134_; lean_object* v_val_135_; 
v___x_134_ = lean_apply_1(v_t_132_, v_a_133_);
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_134_);
return v_val_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg___lam__1(lean_object* v_t_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; lean_object* v_inv_139_; 
v___x_138_ = lean_apply_1(v_t_136_, v_a_137_);
v_inv_139_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_inv_139_);
lean_dec_ref(v___x_138_);
return v_inv_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg(lean_object* v_inst_140_, lean_object* v_N_141_, lean_object* v_t_142_){
_start:
{
lean_object* v_toSemiring_143_; lean_object* v___x_144_; lean_object* v_toZero_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_157_; 
v_toSemiring_143_ = lean_ctor_get(v_inst_140_, 0);
lean_inc_ref(v_toSemiring_143_);
lean_dec_ref(v_inst_140_);
v___x_144_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_143_);
v_toZero_145_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_144_, 0);
lean_dec(v_unused_158_);
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_157_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_toZero_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_157_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_inc_ref(v_t_142_);
v___f_149_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_diagGL___redArg___lam__0), 2, 1);
lean_closure_set(v___f_149_, 0, v_t_142_);
v___f_150_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_diagGL___redArg___lam__1), 2, 1);
lean_closure_set(v___f_150_, 0, v_t_142_);
v___x_151_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_151_, 0, v_N_141_);
lean_inc(v_toZero_145_);
lean_inc_ref(v___x_151_);
v___x_152_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_152_, 0, lean_box(0));
lean_closure_set(v___x_152_, 1, lean_box(0));
lean_closure_set(v___x_152_, 2, v___x_151_);
lean_closure_set(v___x_152_, 3, v_toZero_145_);
lean_closure_set(v___x_152_, 4, v___f_149_);
v___x_153_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, v___x_151_);
lean_closure_set(v___x_153_, 3, v_toZero_145_);
lean_closure_set(v___x_153_, 4, v___f_150_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___x_153_);
lean_ctor_set(v___x_147_, 0, v___x_152_);
v___x_155_ = v___x_147_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_diagGL(lean_object* v_R_159_, lean_object* v_inst_160_, lean_object* v_N_161_, lean_object* v_t_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lp_tree_Formalism_BasicNotions_diagGL___redArg(v_inst_160_, v_N_161_, v_t_162_);
return v___x_163_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementB(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementW(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataCoeff(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
