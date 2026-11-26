// Lean compiler output
// Module: Lib.Weil.Lift
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.Cuspidality public import Lib.DiscreteSeries.Theta.BlockRule public import Lib.DiscreteSeries.Theta.LocalCorrespondence public import Lib.Weil.DualPair.ThetaLiftConvergence
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
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib_Pi_instStarAddMonoidForall___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_restrict___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_prodComm___redArg();
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
extern lean_object* lp_mathlib_Nat_instLocallyFiniteOrder;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_FockDualPair_vacuumWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Ioo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___closed__1;
static const lean_closure_object lp_GRH_New_staircaseWeight___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_staircaseWeight___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_staircaseWeight___redArg___closed__2 = (const lean_object*)&lp_GRH_New_staircaseWeight___redArg___closed__2_value;
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___closed__3;
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___closed__4;
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___closed__5;
static lean_once_cell_t lp_GRH_New_staircaseWeight___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_staircaseWeight___redArg___closed__6;
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_negIf___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_negIf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_negIf(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_negIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_conjForm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_conjForm___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_conjForm___redArg___closed__0 = (const lean_object*)&lp_GRH_New_conjForm___redArg___closed__0_value;
static lean_once_cell_t lp_GRH_New_conjForm___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_conjForm___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_conjForm___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_conjForm___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_conjForm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_conjForm___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_conjForm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0, &lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0_once, _init_lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___lam__0(lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___lam__0___closed__1, &lp_GRH_New_staircaseWeight___redArg___lam__0___closed__1_once, _init_lp_GRH_New_staircaseWeight___redArg___lam__0___closed__1);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___lam__0___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_staircaseWeight___redArg___lam__0(v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___lam__1(lean_object* v_k_9_, lean_object* v___x_10_, lean_object* v_j_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_2(v_k_9_, v___x_10_, v_j_11_);
return v___x_12_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0, &lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0_once, _init_lp_GRH_New_staircaseWeight___redArg___lam__0___closed__0);
v___x_14_ = lean_int_neg(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___closed__0, &lp_GRH_New_staircaseWeight___redArg___closed__0_once, _init_lp_GRH_New_staircaseWeight___redArg___closed__0);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___closed__3(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___closed__4(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_mathlib_Equiv_refl___redArg();
return v___x_20_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___closed__5(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_mathlib_Equiv_prodComm___redArg();
return v___x_21_;
}
}
static lean_object* _init_lp_GRH_New_staircaseWeight___redArg___closed__6(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___closed__4, &lp_GRH_New_staircaseWeight___redArg___closed__4_once, _init_lp_GRH_New_staircaseWeight___redArg___closed__4);
v___x_23_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___closed__5, &lp_GRH_New_staircaseWeight___redArg___closed__5_once, _init_lp_GRH_New_staircaseWeight___redArg___closed__5);
v___x_24_ = lp_mathlib_Equiv_trans___redArg(v___x_23_, v___x_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg(lean_object* v_inst_25_, lean_object* v_s_26_, lean_object* v_o_27_, lean_object* v_k_28_, lean_object* v_00_u03b3_29_, lean_object* v_c_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_val_35_; lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_31_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_32_ = lp_mathlib_Nat_instLocallyFiniteOrder;
v___x_33_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___closed__1, &lp_GRH_New_staircaseWeight___redArg___closed__1_once, _init_lp_GRH_New_staircaseWeight___redArg___closed__1);
lean_inc(v_c_30_);
v___x_34_ = lean_apply_1(v_s_26_, v_c_30_);
v_val_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_35_);
v___x_36_ = l_List_lengthTR___redArg(v_inst_25_);
v___f_37_ = ((lean_object*)(lp_GRH_New_staircaseWeight___redArg___closed__2));
v___x_38_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___closed__3, &lp_GRH_New_staircaseWeight___redArg___closed__3_once, _init_lp_GRH_New_staircaseWeight___redArg___closed__3);
lean_inc(v___x_36_);
v___x_39_ = lean_nat_to_int(v___x_36_);
v___x_40_ = lean_int_add(v_00_u03b3_29_, v___x_39_);
lean_dec(v___x_39_);
v___x_41_ = lean_obj_once(&lp_GRH_New_staircaseWeight___redArg___closed__6, &lp_GRH_New_staircaseWeight___redArg___closed__6_once, _init_lp_GRH_New_staircaseWeight___redArg___closed__6);
v___x_42_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_42_, 0, v___x_33_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_38_);
lean_ctor_set(v___x_42_, 3, v___x_41_);
lean_inc_ref(v___x_34_);
v___f_43_ = lean_alloc_closure((void*)(lp_GRH_New_staircaseWeight___redArg___lam__1), 3, 2);
lean_closure_set(v___f_43_, 0, v_k_28_);
lean_closure_set(v___f_43_, 1, v___x_34_);
v___x_44_ = lp_GRH_New_FockDualPair_vacuumWeight___redArg(v_inst_25_, v___f_37_, v___x_42_, v___x_34_);
v___x_45_ = lean_apply_1(v_o_27_, v_c_30_);
v___x_46_ = lp_mathlib_Finset_Ioo___redArg(v___x_32_, v___x_45_, v___x_36_);
v___x_47_ = lp_mathlib_Finset_sum___redArg(v___x_31_, v___x_46_, v___f_43_);
v___x_48_ = lean_nat_to_int(v___x_47_);
v___x_49_ = lean_int_mul(v_val_35_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v_val_35_);
v___x_50_ = lean_int_sub(v___x_44_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_44_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___redArg___boxed(lean_object* v_inst_51_, lean_object* v_s_52_, lean_object* v_o_53_, lean_object* v_k_54_, lean_object* v_00_u03b3_55_, lean_object* v_c_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_GRH_New_staircaseWeight___redArg(v_inst_51_, v_s_52_, v_o_53_, v_k_54_, v_00_u03b3_55_, v_c_56_);
lean_dec(v_00_u03b3_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight(lean_object* v_n_58_, lean_object* v_inst_59_, lean_object* v_r_60_, lean_object* v_s_61_, lean_object* v_o_62_, lean_object* v_k_63_, lean_object* v_00_u03b3_64_, lean_object* v_c_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lp_GRH_New_staircaseWeight___redArg(v_inst_59_, v_s_61_, v_o_62_, v_k_63_, v_00_u03b3_64_, v_c_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_staircaseWeight___boxed(lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_r_69_, lean_object* v_s_70_, lean_object* v_o_71_, lean_object* v_k_72_, lean_object* v_00_u03b3_73_, lean_object* v_c_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_GRH_New_staircaseWeight(v_n_67_, v_inst_68_, v_r_69_, v_s_70_, v_o_71_, v_k_72_, v_00_u03b3_73_, v_c_74_);
lean_dec(v_00_u03b3_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_negIf___redArg(lean_object* v_inst_76_, uint8_t v_d_77_, lean_object* v_l_78_){
_start:
{
if (v_d_77_ == 0)
{
lean_dec(v_inst_76_);
return v_l_78_;
}
else
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_1(v_inst_76_, v_l_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_negIf___redArg___boxed(lean_object* v_inst_80_, lean_object* v_d_81_, lean_object* v_l_82_){
_start:
{
uint8_t v_d_boxed_83_; lean_object* v_res_84_; 
v_d_boxed_83_ = lean_unbox(v_d_81_);
v_res_84_ = lp_GRH_New_negIf___redArg(v_inst_80_, v_d_boxed_83_, v_l_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_negIf(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, uint8_t v_d_87_, lean_object* v_l_88_){
_start:
{
if (v_d_87_ == 0)
{
lean_dec(v_inst_86_);
return v_l_88_;
}
else
{
lean_object* v___x_89_; 
v___x_89_ = lean_apply_1(v_inst_86_, v_l_88_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_negIf___boxed(lean_object* v_00_u03b1_90_, lean_object* v_inst_91_, lean_object* v_d_92_, lean_object* v_l_93_){
_start:
{
uint8_t v_d_boxed_94_; lean_object* v_res_95_; 
v_d_boxed_94_ = lean_unbox(v_d_92_);
v_res_95_ = lp_GRH_New_negIf(v_00_u03b1_90_, v_inst_91_, v_d_boxed_94_, v_l_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg___lam__0(lean_object* v_i_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_mathlib_Complex_instStarRing___lam__0(v___y_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg___lam__0___boxed(lean_object* v_i_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_GRH_New_conjForm___redArg___lam__0(v_i_99_, v___y_100_);
lean_dec_ref(v_i_99_);
return v_res_101_;
}
}
static lean_object* _init_lp_GRH_New_conjForm___redArg___closed__1(void){
_start:
{
lean_object* v___f_103_; lean_object* v___x_104_; 
v___f_103_ = ((lean_object*)(lp_GRH_New_conjForm___redArg___closed__0));
v___x_104_ = lp_mathlib_Pi_instStarAddMonoidForall___redArg(v___f_103_);
return v___x_104_;
}
}
static lean_object* _init_lp_GRH_New_conjForm___redArg___closed__2(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&lp_GRH_New_conjForm___redArg___closed__1, &lp_GRH_New_conjForm___redArg___closed__1_once, _init_lp_GRH_New_conjForm___redArg___closed__1);
v___x_106_ = lp_mathlib_LinearMap_restrict___redArg(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg(){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&lp_GRH_New_conjForm___redArg___closed__2, &lp_GRH_New_conjForm___redArg___closed__2_once, _init_lp_GRH_New_conjForm___redArg___closed__2);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_GRH_New_conjForm___redArg();
return v_res_110_;
}
}
static lean_object* _init_lp_GRH_New_conjForm___closed__0(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lp_GRH_New_conjForm___redArg();
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_conjForm(lean_object* v_E_112_, lean_object* v_n_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_s_118_, lean_object* v_S_119_, lean_object* v_e_120_, lean_object* v_e_x27_121_, lean_object* v_h_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&lp_GRH_New_conjForm___closed__0, &lp_GRH_New_conjForm___closed__0_once, _init_lp_GRH_New_conjForm___closed__0);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_conjForm___boxed(lean_object* v_E_124_, lean_object* v_n_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_s_130_, lean_object* v_S_131_, lean_object* v_e_132_, lean_object* v_e_x27_133_, lean_object* v_h_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_GRH_New_conjForm(v_E_124_, v_n_125_, v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_, v_s_130_, v_S_131_, v_e_132_, v_e_x27_133_, v_h_134_);
lean_dec_ref(v_e_x27_133_);
lean_dec_ref(v_e_132_);
lean_dec_ref(v_S_131_);
lean_dec_ref(v_s_130_);
lean_dec_ref(v_inst_129_);
lean_dec(v_inst_128_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
return v_res_135_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_Cuspidality(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_BlockRule(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_LocalCorrespondence(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_ThetaLiftConvergence(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Lift(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_Cuspidality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Theta_BlockRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Theta_LocalCorrespondence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_ThetaLiftConvergence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
