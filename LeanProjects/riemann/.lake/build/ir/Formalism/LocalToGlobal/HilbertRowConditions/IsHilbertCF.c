// Lean compiler output
// Module: Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal public import Formalism.LocalToGlobal.UnitaryNorms.CharTied public import Formalism.LocalToGlobal.Divisibility.LiftLat public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
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
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Rows_getQ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Rows_getQ___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_getQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_getQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_vPar(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Rows_aPlus___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Rows_aPlus___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Rows_aPlus___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Rows_aPlus___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aPlus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aPlus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aMinusAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aMinusAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_kaSmallOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_kaSmallOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Rows_getQ___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_getQ(lean_object* v_n_3_, lean_object* v_f_4_, lean_object* v_i_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_i_5_, v_n_3_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec(v_i_5_);
lean_dec_ref(v_f_4_);
v___x_7_ = lean_obj_once(&lp_tree_Formalism_L2_Rows_getQ___closed__0, &lp_tree_Formalism_L2_Rows_getQ___closed__0_once, _init_lp_tree_Formalism_L2_Rows_getQ___closed__0);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_f_4_, v_i_5_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_getQ___boxed(lean_object* v_n_9_, lean_object* v_f_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_Rows_getQ(v_n_9_, v_f_10_, v_i_11_);
lean_dec(v_n_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_vPar(lean_object* v_D_13_, lean_object* v_00_u03c4_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_R_16_; lean_object* v_hc_17_; lean_object* v_k_18_; lean_object* v_m_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_R_16_ = lean_ctor_get(v_D_13_, 0);
lean_inc_ref(v_R_16_);
v_hc_17_ = lean_ctor_get(v_D_13_, 6);
lean_inc_ref(v_hc_17_);
lean_dec_ref(v_D_13_);
v_k_18_ = lean_ctor_get(v_R_16_, 1);
lean_inc(v_k_18_);
v_m_19_ = lean_ctor_get(v_R_16_, 2);
lean_inc(v_m_19_);
lean_dec_ref(v_R_16_);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_nat_sub(v_k_18_, v___x_20_);
lean_dec(v_k_18_);
v___x_22_ = lean_nat_dec_lt(v_i_15_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v_b_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = lean_apply_1(v_hc_17_, v_00_u03c4_14_);
v_b_24_ = lean_ctor_get(v___x_23_, 2);
lean_inc_ref(v_b_24_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_nat_sub(v_i_15_, v___x_21_);
lean_dec(v___x_21_);
lean_dec(v_i_15_);
v___x_26_ = lp_tree_Formalism_L2_Rows_getQ(v_m_19_, v_b_24_, v___x_25_);
lean_dec(v_m_19_);
v___x_27_ = l_Rat_neg(v___x_26_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v_v_29_; lean_object* v___x_30_; 
lean_dec(v_m_19_);
v___x_28_ = lean_apply_1(v_hc_17_, v_00_u03c4_14_);
v_v_29_ = lean_ctor_get(v___x_28_, 1);
lean_inc_ref(v_v_29_);
lean_dec_ref(v___x_28_);
v___x_30_ = lp_tree_Formalism_L2_Rows_getQ(v___x_21_, v_v_29_, v_i_15_);
lean_dec(v___x_21_);
return v___x_30_;
}
}
}
static lean_object* _init_lp_tree_Formalism_L2_Rows_aPlus___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Rows_aPlus___closed__1(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(2u);
v___x_34_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aPlus(lean_object* v_D_35_, lean_object* v_j_36_, lean_object* v_00_u03c4_37_, lean_object* v_i_38_){
_start:
{
lean_object* v_R_39_; lean_object* v_hc_40_; lean_object* v_m_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_e_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_R_39_ = lean_ctor_get(v_D_35_, 0);
lean_inc_ref(v_R_39_);
v_hc_40_ = lean_ctor_get(v_D_35_, 6);
lean_inc_ref(v_hc_40_);
v_m_41_ = lean_ctor_get(v_R_39_, 2);
lean_inc(v_m_41_);
lean_inc(v_i_38_);
lean_inc(v_00_u03c4_37_);
v___x_42_ = lp_tree_Formalism_L2_Rows_vPar(v_D_35_, v_00_u03c4_37_, v_i_38_);
v___x_43_ = lean_apply_1(v_hc_40_, v_00_u03c4_37_);
v_e_44_ = lean_ctor_get(v___x_43_, 3);
lean_inc_ref(v_e_44_);
lean_dec_ref(v___x_43_);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_sub(v_j_36_, v___x_45_);
v___x_47_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_39_);
v___x_48_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_47_);
v___x_49_ = lean_obj_once(&lp_tree_Formalism_L2_Rows_aPlus___closed__0, &lp_tree_Formalism_L2_Rows_aPlus___closed__0_once, _init_lp_tree_Formalism_L2_Rows_aPlus___closed__0);
v___x_50_ = l_Rat_add(v___x_48_, v___x_49_);
v___x_51_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_39_, v_j_36_);
lean_dec_ref(v_R_39_);
v_fst_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_fst_52_);
v_snd_53_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_snd_53_);
lean_dec_ref(v___x_51_);
v___x_54_ = lean_obj_once(&lp_tree_Formalism_L2_Rows_aPlus___closed__1, &lp_tree_Formalism_L2_Rows_aPlus___closed__1_once, _init_lp_tree_Formalism_L2_Rows_aPlus___closed__1);
v___x_55_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_38_);
v___x_56_ = l_Rat_add(v___x_55_, v___x_49_);
v___x_57_ = l_Rat_mul(v___x_54_, v___x_56_);
v___x_58_ = lp_tree_Formalism_L2_Rows_getQ(v_m_41_, v_e_44_, v___x_46_);
lean_dec(v_m_41_);
v___x_59_ = l_Rat_add(v___x_42_, v___x_58_);
v___x_60_ = l_Rat_sub(v___x_50_, v___x_57_);
v___x_61_ = l_Rat_div(v___x_60_, v___x_54_);
lean_dec_ref(v___x_60_);
v___x_62_ = l_Rat_sub(v___x_59_, v___x_61_);
v___x_63_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_fst_52_);
v___x_64_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_snd_53_);
v___x_65_ = l_Rat_sub(v___x_63_, v___x_64_);
v___x_66_ = l_Rat_div(v___x_65_, v___x_54_);
lean_dec_ref(v___x_65_);
v___x_67_ = l_Rat_sub(v___x_62_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aPlus___boxed(lean_object* v_D_68_, lean_object* v_j_69_, lean_object* v_00_u03c4_70_, lean_object* v_i_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_Formalism_L2_Rows_aPlus(v_D_68_, v_j_69_, v_00_u03c4_70_, v_i_71_);
lean_dec(v_j_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aMinusAt(lean_object* v_D_73_, lean_object* v_j_74_, lean_object* v_00_u03c4_75_, lean_object* v_c_u2080_76_){
_start:
{
lean_object* v_R_77_; lean_object* v_hc_78_; lean_object* v_m_79_; lean_object* v_t_80_; lean_object* v___x_81_; lean_object* v_b_82_; lean_object* v_e_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_R_77_ = lean_ctor_get(v_D_73_, 0);
lean_inc_ref(v_R_77_);
v_hc_78_ = lean_ctor_get(v_D_73_, 6);
lean_inc_ref(v_hc_78_);
lean_dec_ref(v_D_73_);
v_m_79_ = lean_ctor_get(v_R_77_, 2);
lean_inc(v_m_79_);
v_t_80_ = lean_ctor_get(v_R_77_, 3);
lean_inc(v_t_80_);
lean_dec_ref(v_R_77_);
v___x_81_ = lean_apply_1(v_hc_78_, v_00_u03c4_75_);
v_b_82_ = lean_ctor_get(v___x_81_, 2);
lean_inc_ref(v_b_82_);
v_e_83_ = lean_ctor_get(v___x_81_, 3);
lean_inc_ref(v_e_83_);
lean_dec_ref(v___x_81_);
v___x_84_ = lean_nat_add(v_j_74_, v_c_u2080_76_);
v___x_85_ = lp_tree_Formalism_L2_Rows_getQ(v_m_79_, v_b_82_, v___x_84_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_sub(v_j_74_, v___x_86_);
v___x_88_ = lp_tree_Formalism_L2_Rows_getQ(v_m_79_, v_e_83_, v___x_87_);
lean_dec(v_m_79_);
v___x_89_ = l_Rat_sub(v___x_85_, v___x_88_);
v___x_90_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_80_);
v___x_91_ = lean_obj_once(&lp_tree_Formalism_L2_Rows_aPlus___closed__0, &lp_tree_Formalism_L2_Rows_aPlus___closed__0_once, _init_lp_tree_Formalism_L2_Rows_aPlus___closed__0);
v___x_92_ = l_Rat_sub(v___x_90_, v___x_91_);
v___x_93_ = lean_obj_once(&lp_tree_Formalism_L2_Rows_aPlus___closed__1, &lp_tree_Formalism_L2_Rows_aPlus___closed__1_once, _init_lp_tree_Formalism_L2_Rows_aPlus___closed__1);
v___x_94_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_c_u2080_76_);
v___x_95_ = l_Rat_add(v___x_94_, v___x_91_);
v___x_96_ = l_Rat_mul(v___x_93_, v___x_95_);
v___x_97_ = l_Rat_add(v___x_92_, v___x_96_);
v___x_98_ = l_Rat_div(v___x_97_, v___x_93_);
lean_dec_ref(v___x_97_);
v___x_99_ = l_Rat_sub(v___x_89_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_aMinusAt___boxed(lean_object* v_D_100_, lean_object* v_j_101_, lean_object* v_00_u03c4_102_, lean_object* v_c_u2080_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_tree_Formalism_L2_Rows_aMinusAt(v_D_100_, v_j_101_, v_00_u03c4_102_, v_c_u2080_103_);
lean_dec(v_j_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_kaSmallOf(lean_object* v_D_105_, lean_object* v_j_106_, lean_object* v_00_u03c4_107_, lean_object* v_c_u2080_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lp_tree_Formalism_L2_Rows_aMinusAt(v_D_105_, v_j_106_, v_00_u03c4_107_, v_c_u2080_108_);
v___x_110_ = l_Rat_neg(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Rows_kaSmallOf___boxed(lean_object* v_D_111_, lean_object* v_j_112_, lean_object* v_00_u03c4_113_, lean_object* v_c_u2080_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = lp_tree_Formalism_L2_Rows_kaSmallOf(v_D_111_, v_j_112_, v_00_u03c4_113_, v_c_u2080_114_);
lean_dec(v_j_112_);
return v_res_115_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_MemFIffReal(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharTied(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HilbertRowConditions_IsHilbertCF(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_MemFIffReal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharTied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
