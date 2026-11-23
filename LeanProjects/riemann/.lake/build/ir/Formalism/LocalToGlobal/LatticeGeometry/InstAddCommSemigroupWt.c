// Lean compiler output
// Module: Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply public import Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_WithZero_recZeroCoe___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_mathlib_SubsemiringClass_subtype___lam__0___boxed(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Geo_wtOfN___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Geo_wtOfN___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_instAddCommSemigroupWt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Mlat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Mlat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubsemiringClass_subtype___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__1_value;
static const lean_closure_object lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_RingHom_comp___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__1_value),((lean_object*)&lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__2 = (const lean_object*)&lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_FormsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_FormsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_scal___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_scal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_scal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cfF___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cfF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cfF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_toWeightFamilies___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_toWeightFamilies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_sig0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_sig0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_sig0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Geo_wtOfN___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN___redArg(lean_object* v_D_3_, lean_object* v_j_4_, lean_object* v_w_5_, lean_object* v_00_u03c4_6_, lean_object* v_i_7_){
_start:
{
lean_object* v_R_8_; lean_object* v___x_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; uint8_t v___x_12_; 
v_R_8_ = lean_ctor_get(v_D_3_, 0);
v___x_9_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_8_, v_j_4_);
v_fst_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_snd_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_nat_dec_lt(v_i_7_, v_fst_10_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = lean_nat_sub(v_i_7_, v_fst_10_);
lean_dec(v_fst_10_);
lean_dec(v_i_7_);
v___x_14_ = lean_nat_dec_lt(v___x_13_, v_snd_11_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec(v___x_13_);
lean_dec(v_snd_11_);
lean_dec(v_00_u03c4_6_);
lean_dec_ref(v_w_5_);
v___x_15_ = lean_obj_once(&lp_tree_Formalism_L2_Geo_wtOfN___redArg___closed__0, &lp_tree_Formalism_L2_Geo_wtOfN___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Geo_wtOfN___redArg___closed__0);
return v___x_15_;
}
else
{
lean_object* v_aM_16_; lean_object* v_n_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_aM_16_ = lean_ctor_get(v_w_5_, 1);
lean_inc_ref(v_aM_16_);
v_n_17_ = lean_ctor_get(v_w_5_, 2);
lean_inc(v_n_17_);
lean_dec_ref(v_w_5_);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v___x_13_, v___x_18_);
lean_dec(v___x_13_);
v___x_20_ = lean_nat_sub(v_snd_11_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v_snd_11_);
v___x_21_ = lean_apply_2(v_aM_16_, v_00_u03c4_6_, v___x_20_);
v___x_22_ = lean_nat_to_int(v___x_21_);
v___x_23_ = lean_int_neg(v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_nat_shiftr(v_n_17_, v___x_18_);
lean_dec(v_n_17_);
v___x_25_ = lean_nat_to_int(v___x_24_);
v___x_26_ = lean_int_sub(v___x_23_, v___x_25_);
lean_dec(v___x_25_);
lean_dec(v___x_23_);
return v___x_26_;
}
}
else
{
lean_object* v_aP_27_; lean_object* v_n_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_snd_11_);
lean_dec(v_fst_10_);
v_aP_27_ = lean_ctor_get(v_w_5_, 0);
lean_inc_ref(v_aP_27_);
v_n_28_ = lean_ctor_get(v_w_5_, 2);
lean_inc(v_n_28_);
lean_dec_ref(v_w_5_);
v___x_29_ = lean_apply_2(v_aP_27_, v_00_u03c4_6_, v_i_7_);
v___x_30_ = lean_nat_to_int(v___x_29_);
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_shiftr(v_n_28_, v___x_31_);
lean_dec(v_n_28_);
v___x_33_ = lean_nat_to_int(v___x_32_);
v___x_34_ = lean_int_add(v___x_30_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v___x_30_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN___redArg___boxed(lean_object* v_D_35_, lean_object* v_j_36_, lean_object* v_w_37_, lean_object* v_00_u03c4_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Geo_wtOfN___redArg(v_D_35_, v_j_36_, v_w_37_, v_00_u03c4_38_, v_i_39_);
lean_dec(v_j_36_);
lean_dec_ref(v_D_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN(lean_object* v_D_41_, lean_object* v_j_42_, lean_object* v_N_43_, lean_object* v_w_44_, lean_object* v_00_u03c4_45_, lean_object* v_i_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_L2_Geo_wtOfN___redArg(v_D_41_, v_j_42_, v_w_44_, v_00_u03c4_45_, v_i_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOfN___boxed(lean_object* v_D_48_, lean_object* v_j_49_, lean_object* v_N_50_, lean_object* v_w_51_, lean_object* v_00_u03c4_52_, lean_object* v_i_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_L2_Geo_wtOfN(v_D_48_, v_j_49_, v_N_50_, v_w_51_, v_00_u03c4_52_, v_i_53_);
lean_dec(v_N_50_);
lean_dec(v_j_49_);
lean_dec_ref(v_D_48_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOf(lean_object* v_D_55_, lean_object* v_j_56_, lean_object* v_w_57_, lean_object* v_00_u03c4_58_, lean_object* v_i_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_tree_Formalism_L2_Geo_wtOfN___redArg(v_D_55_, v_j_56_, v_w_57_, v_00_u03c4_58_, v_i_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_wtOf___boxed(lean_object* v_D_61_, lean_object* v_j_62_, lean_object* v_w_63_, lean_object* v_00_u03c4_64_, lean_object* v_i_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_L2_Geo_wtOf(v_D_61_, v_j_62_, v_w_63_, v_00_u03c4_64_, v_i_65_);
lean_dec(v_j_62_);
lean_dec_ref(v_D_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_instAddCommSemigroupWt(lean_object* v_D_67_, lean_object* v_j_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___boxed), 4, 2);
lean_closure_set(v___x_69_, 0, v_D_67_);
lean_closure_set(v___x_69_, 1, v_j_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Mlat(lean_object* v_D_70_, lean_object* v_G_71_, lean_object* v_NW_72_, lean_object* v_CompW_73_, lean_object* v_inst_74_, lean_object* v_algW_75_, lean_object* v_PtY_76_, lean_object* v_P_77_, lean_object* v_j_78_, lean_object* v_w_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Mlat___boxed(lean_object* v_D_81_, lean_object* v_G_82_, lean_object* v_NW_83_, lean_object* v_CompW_84_, lean_object* v_inst_85_, lean_object* v_algW_86_, lean_object* v_PtY_87_, lean_object* v_P_88_, lean_object* v_j_89_, lean_object* v_w_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_Formalism_L2_Geo_FormsPkg_Mlat(v_D_81_, v_G_82_, v_NW_83_, v_CompW_84_, v_inst_85_, v_algW_86_, v_PtY_87_, v_P_88_, v_j_89_, v_w_90_);
lean_dec_ref(v_w_90_);
lean_dec(v_j_89_);
lean_dec_ref(v_P_88_);
lean_dec_ref(v_algW_86_);
lean_dec(v_inst_85_);
lean_dec_ref(v_NW_83_);
lean_dec_ref(v_G_82_);
lean_dec_ref(v_D_81_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__0(lean_object* v_G_92_, lean_object* v_algW_93_, lean_object* v_j_94_, lean_object* v_i_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_fnAlg_97_; lean_object* v___x_98_; lean_object* v_Yv_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_algebraMap_102_; lean_object* v___x_103_; 
v_fnAlg_97_ = lean_ctor_get(v_G_92_, 2);
lean_inc_ref(v_fnAlg_97_);
lean_dec_ref(v_G_92_);
v___x_98_ = lean_apply_1(v_algW_93_, v_j_94_);
v_Yv_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_Yv_99_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_apply_1(v_Yv_99_, v_i_95_);
v___x_101_ = lean_apply_1(v_fnAlg_97_, v___x_100_);
v_algebraMap_102_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_algebraMap_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = lean_apply_1(v_algebraMap_102_, v___y_96_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__1(lean_object* v_G_104_, lean_object* v_algW_105_, lean_object* v_j_106_, lean_object* v_kL_107_, lean_object* v___f_108_, lean_object* v_c_109_, lean_object* v_x_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_fnField_112_; lean_object* v___x_113_; lean_object* v_Yv_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_toCommSemiring_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_toMul_121_; lean_object* v___x_277__overap_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_fnField_112_ = lean_ctor_get(v_G_104_, 1);
lean_inc_ref(v_fnField_112_);
lean_dec_ref(v_G_104_);
v___x_113_ = lean_apply_1(v_algW_105_, v_j_106_);
v_Yv_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_Yv_114_);
lean_dec_ref(v___x_113_);
lean_inc_n(v___y_111_, 2);
v___x_115_ = lean_apply_1(v_Yv_114_, v___y_111_);
v___x_116_ = lean_apply_1(v_fnField_112_, v___x_115_);
v___x_117_ = lp_mathlib_Field_toSemifield___redArg(v___x_116_);
lean_dec_ref(v___x_116_);
v_toCommSemiring_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_toCommSemiring_118_);
lean_dec_ref(v___x_117_);
v___x_119_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toCommSemiring_118_);
lean_dec_ref(v_toCommSemiring_118_);
v___x_120_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_119_);
v_toMul_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_toMul_121_);
lean_dec_ref(v___x_120_);
v___x_277__overap_122_ = lp_mathlib_RingHom_comp___redArg___lam__0(v_kL_107_, v___f_108_, v_c_109_);
v___x_123_ = lean_apply_1(v___x_277__overap_122_, v___y_111_);
v___x_124_ = lean_apply_1(v_x_110_, v___y_111_);
v___x_125_ = lean_apply_2(v_toMul_121_, v___x_123_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg(lean_object* v_G_126_, lean_object* v_algW_127_, lean_object* v_P_128_, lean_object* v_j_129_){
_start:
{
lean_object* v_kL_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v_kL_130_ = lean_ctor_get(v_P_128_, 2);
lean_inc_n(v_kL_130_, 2);
lean_dec_ref(v_P_128_);
lean_inc(v_j_129_);
lean_inc_ref(v_algW_127_);
lean_inc_ref(v_G_126_);
v___f_131_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__0), 5, 3);
lean_closure_set(v___f_131_, 0, v_G_126_);
lean_closure_set(v___f_131_, 1, v_algW_127_);
lean_closure_set(v___f_131_, 2, v_j_129_);
v___f_132_ = lean_alloc_closure((void*)(lp_mathlib_NonUnitalRingHom_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_132_, 0, v___f_131_);
lean_inc_ref(v___f_132_);
v___f_133_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__1), 8, 5);
lean_closure_set(v___f_133_, 0, v_G_126_);
lean_closure_set(v___f_133_, 1, v_algW_127_);
lean_closure_set(v___f_133_, 2, v_j_129_);
lean_closure_set(v___f_133_, 3, v_kL_130_);
lean_closure_set(v___f_133_, 4, v___f_132_);
v___f_134_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_134_, 0, v_kL_130_);
lean_closure_set(v___f_134_, 1, v___f_132_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___f_133_);
lean_ctor_set(v___x_135_, 1, v___f_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT(lean_object* v_D_136_, lean_object* v_G_137_, lean_object* v_NW_138_, lean_object* v_CompW_139_, lean_object* v_inst_140_, lean_object* v_algW_141_, lean_object* v_PtY_142_, lean_object* v_P_143_, lean_object* v_j_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg(v_G_137_, v_algW_141_, v_P_143_, v_j_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___boxed(lean_object* v_D_146_, lean_object* v_G_147_, lean_object* v_NW_148_, lean_object* v_CompW_149_, lean_object* v_inst_150_, lean_object* v_algW_151_, lean_object* v_PtY_152_, lean_object* v_P_153_, lean_object* v_j_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT(v_D_146_, v_G_147_, v_NW_148_, v_CompW_149_, v_inst_150_, v_algW_151_, v_PtY_152_, v_P_153_, v_j_154_);
lean_dec(v_inst_150_);
lean_dec_ref(v_NW_148_);
lean_dec_ref(v_D_146_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___lam__1(lean_object* v_G_156_, lean_object* v_algW_157_, lean_object* v_j_158_, lean_object* v___f_159_, lean_object* v___f_160_, lean_object* v_c_161_, lean_object* v_x_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_fnField_164_; lean_object* v___x_165_; lean_object* v_Yv_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_toCommSemiring_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_toMul_173_; lean_object* v___x_350__overap_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_fnField_164_ = lean_ctor_get(v_G_156_, 1);
lean_inc_ref(v_fnField_164_);
lean_dec_ref(v_G_156_);
v___x_165_ = lean_apply_1(v_algW_157_, v_j_158_);
v_Yv_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_Yv_166_);
lean_dec_ref(v___x_165_);
lean_inc_n(v___y_163_, 2);
v___x_167_ = lean_apply_1(v_Yv_166_, v___y_163_);
v___x_168_ = lean_apply_1(v_fnField_164_, v___x_167_);
v___x_169_ = lp_mathlib_Field_toSemifield___redArg(v___x_168_);
lean_dec_ref(v___x_168_);
v_toCommSemiring_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_toCommSemiring_170_);
lean_dec_ref(v___x_169_);
v___x_171_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toCommSemiring_170_);
lean_dec_ref(v_toCommSemiring_170_);
v___x_172_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_171_);
v_toMul_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_toMul_173_);
lean_dec_ref(v___x_172_);
v___x_350__overap_174_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_159_, v___f_160_, v_c_161_);
v___x_175_ = lean_apply_1(v___x_350__overap_174_, v___y_163_);
v___x_176_ = lean_apply_1(v_x_162_, v___y_163_);
v___x_177_ = lean_apply_2(v_toMul_173_, v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg(lean_object* v_G_183_, lean_object* v_algW_184_, lean_object* v_P_185_, lean_object* v_j_186_){
_start:
{
lean_object* v_kL_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_194_; 
v_kL_187_ = lean_ctor_get(v_P_185_, 2);
lean_inc(v_kL_187_);
lean_dec_ref(v_P_185_);
lean_inc(v_j_186_);
lean_inc_ref(v_algW_184_);
lean_inc_ref(v_G_183_);
v___f_188_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraKOFnT___redArg___lam__0), 5, 3);
lean_closure_set(v___f_188_, 0, v_G_183_);
lean_closure_set(v___f_188_, 1, v_algW_184_);
lean_closure_set(v___f_188_, 2, v_j_186_);
v___f_189_ = lean_alloc_closure((void*)(lp_mathlib_NonUnitalRingHom_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_189_, 0, v___f_188_);
v___f_190_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_190_, 0, v_kL_187_);
lean_closure_set(v___f_190_, 1, v___f_189_);
v___f_191_ = ((lean_object*)(lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___closed__2));
lean_inc_ref(v___f_190_);
v___f_192_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg___lam__1), 8, 5);
lean_closure_set(v___f_192_, 0, v_G_183_);
lean_closure_set(v___f_192_, 1, v_algW_184_);
lean_closure_set(v___f_192_, 2, v_j_186_);
lean_closure_set(v___f_192_, 3, v___f_191_);
lean_closure_set(v___f_192_, 4, v___f_190_);
v___f_193_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_193_, 0, v___f_191_);
lean_closure_set(v___f_193_, 1, v___f_190_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___f_192_);
lean_ctor_set(v___x_194_, 1, v___f_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT(lean_object* v_D_195_, lean_object* v_G_196_, lean_object* v_NW_197_, lean_object* v_CompW_198_, lean_object* v_inst_199_, lean_object* v_algW_200_, lean_object* v_PtY_201_, lean_object* v_P_202_, lean_object* v_j_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___redArg(v_G_196_, v_algW_200_, v_P_202_, v_j_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT___boxed(lean_object* v_D_205_, lean_object* v_G_206_, lean_object* v_NW_207_, lean_object* v_CompW_208_, lean_object* v_inst_209_, lean_object* v_algW_210_, lean_object* v_PtY_211_, lean_object* v_P_212_, lean_object* v_j_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = lp_tree_Formalism_L2_Geo_FormsPkg_instAlgebraRingOfIntegersKOFnT(v_D_205_, v_G_206_, v_NW_207_, v_CompW_208_, v_inst_209_, v_algW_210_, v_PtY_211_, v_P_212_, v_j_213_);
lean_dec(v_inst_209_);
lean_dec_ref(v_NW_207_);
lean_dec_ref(v_D_205_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg___lam__0(lean_object* v_cmp_215_, lean_object* v_j_216_, lean_object* v_w_217_, lean_object* v_F_218_, lean_object* v_c_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_apply_4(v_cmp_215_, v_j_216_, v_w_217_, v_c_219_, v_F_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg___lam__1(lean_object* v_cmp_221_, lean_object* v_j_222_, lean_object* v_w_223_, lean_object* v_toZero_224_, lean_object* v_F_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; 
v___f_226_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg___lam__0), 5, 4);
lean_closure_set(v___f_226_, 0, v_cmp_221_);
lean_closure_set(v___f_226_, 1, v_j_222_);
lean_closure_set(v___f_226_, 2, v_w_223_);
lean_closure_set(v___f_226_, 3, v_F_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_toZero_224_);
lean_ctor_set(v___x_227_, 1, v___f_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg(lean_object* v_P_228_, lean_object* v_j_229_, lean_object* v_w_230_){
_start:
{
lean_object* v_fKO_231_; lean_object* v_cmp_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_toSemiring_235_; lean_object* v___x_236_; lean_object* v_toZero_237_; lean_object* v___f_238_; 
v_fKO_231_ = lean_ctor_get(v_P_228_, 0);
lean_inc_ref(v_fKO_231_);
v_cmp_232_ = lean_ctor_get(v_P_228_, 6);
lean_inc(v_cmp_232_);
lean_dec_ref(v_P_228_);
v___x_233_ = lp_mathlib_Field_toSemifield___redArg(v_fKO_231_);
lean_dec_ref(v_fKO_231_);
v___x_234_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_233_);
v_toSemiring_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_toSemiring_235_);
lean_dec_ref(v___x_234_);
v___x_236_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_235_);
v_toZero_237_ = lean_ctor_get(v___x_236_, 1);
lean_inc(v_toZero_237_);
lean_dec_ref(v___x_236_);
v___f_238_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg___lam__1), 5, 4);
lean_closure_set(v___f_238_, 0, v_cmp_232_);
lean_closure_set(v___f_238_, 1, v_j_229_);
lean_closure_set(v___f_238_, 2, v_w_230_);
lean_closure_set(v___f_238_, 3, v_toZero_237_);
return v___f_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup(lean_object* v_D_239_, lean_object* v_G_240_, lean_object* v_NW_241_, lean_object* v_CompW_242_, lean_object* v_inst_243_, lean_object* v_algW_244_, lean_object* v_PtY_245_, lean_object* v_P_246_, lean_object* v_j_247_, lean_object* v_w_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lp_tree_Formalism_L2_Geo_FormsPkg_tup___redArg(v_P_246_, v_j_247_, v_w_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_tup___boxed(lean_object* v_D_250_, lean_object* v_G_251_, lean_object* v_NW_252_, lean_object* v_CompW_253_, lean_object* v_inst_254_, lean_object* v_algW_255_, lean_object* v_PtY_256_, lean_object* v_P_257_, lean_object* v_j_258_, lean_object* v_w_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = lp_tree_Formalism_L2_Geo_FormsPkg_tup(v_D_250_, v_G_251_, v_NW_252_, v_CompW_253_, v_inst_254_, v_algW_255_, v_PtY_256_, v_P_257_, v_j_258_, v_w_259_);
lean_dec_ref(v_algW_255_);
lean_dec(v_inst_254_);
lean_dec_ref(v_NW_252_);
lean_dec_ref(v_G_251_);
lean_dec_ref(v_D_250_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___lam__0(lean_object* v_w_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___lam__0___boxed(lean_object* v_w_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___lam__0(v_w_263_);
lean_dec_ref(v_w_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg(lean_object* v_m_266_){
_start:
{
lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___f_267_ = ((lean_object*)(lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg___closed__0));
v___x_268_ = lean_box(0);
v___x_269_ = lp_mathlib_WithZero_recZeroCoe___redArg(v___x_268_, v___f_267_, v_m_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm(lean_object* v_D_270_, lean_object* v_G_271_, lean_object* v_NW_272_, lean_object* v_CompW_273_, lean_object* v_inst_274_, lean_object* v_algW_275_, lean_object* v_PtY_276_, lean_object* v_P_277_, lean_object* v_j_278_, lean_object* v_m_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lp_tree_Formalism_L2_Geo_FormsPkg_Vm___redArg(v_m_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_Vm___boxed(lean_object* v_D_281_, lean_object* v_G_282_, lean_object* v_NW_283_, lean_object* v_CompW_284_, lean_object* v_inst_285_, lean_object* v_algW_286_, lean_object* v_PtY_287_, lean_object* v_P_288_, lean_object* v_j_289_, lean_object* v_m_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = lp_tree_Formalism_L2_Geo_FormsPkg_Vm(v_D_281_, v_G_282_, v_NW_283_, v_CompW_284_, v_inst_285_, v_algW_286_, v_PtY_287_, v_P_288_, v_j_289_, v_m_290_);
lean_dec(v_j_289_);
lean_dec_ref(v_P_288_);
lean_dec_ref(v_algW_286_);
lean_dec(v_inst_285_);
lean_dec_ref(v_NW_283_);
lean_dec_ref(v_G_282_);
lean_dec_ref(v_D_281_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_FormsS(lean_object* v_D_292_, lean_object* v_G_293_, lean_object* v_NW_294_, lean_object* v_CompW_295_, lean_object* v_inst_296_, lean_object* v_algW_297_, lean_object* v_PtY_298_, lean_object* v_P_299_, lean_object* v_j_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_FormsS___boxed(lean_object* v_D_302_, lean_object* v_G_303_, lean_object* v_NW_304_, lean_object* v_CompW_305_, lean_object* v_inst_306_, lean_object* v_algW_307_, lean_object* v_PtY_308_, lean_object* v_P_309_, lean_object* v_j_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = lp_tree_Formalism_L2_Geo_FormsPkg_FormsS(v_D_302_, v_G_303_, v_NW_304_, v_CompW_305_, v_inst_306_, v_algW_307_, v_PtY_308_, v_P_309_, v_j_310_);
lean_dec(v_j_310_);
lean_dec_ref(v_P_309_);
lean_dec_ref(v_algW_307_);
lean_dec(v_inst_306_);
lean_dec_ref(v_NW_304_);
lean_dec_ref(v_G_303_);
lean_dec_ref(v_D_302_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg___lam__0(lean_object* v_m_312_, lean_object* v_x_313_){
_start:
{
lean_object* v_toFun_314_; lean_object* v___x_315_; 
v_toFun_314_ = lean_ctor_get(v_x_313_, 1);
lean_inc(v_toFun_314_);
lean_dec_ref(v_x_313_);
v___x_315_ = lean_apply_1(v_toFun_314_, v_m_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg(lean_object* v_m_316_){
_start:
{
lean_object* v___f_317_; 
v___f_317_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg___lam__0), 2, 1);
lean_closure_set(v___f_317_, 0, v_m_316_);
return v___f_317_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf(lean_object* v_D_318_, lean_object* v_G_319_, lean_object* v_NW_320_, lean_object* v_CompW_321_, lean_object* v_inst_322_, lean_object* v_algW_323_, lean_object* v_PtY_324_, lean_object* v_P_325_, lean_object* v_j_326_, lean_object* v_m_327_){
_start:
{
lean_object* v___f_328_; 
v___f_328_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg___lam__0), 2, 1);
lean_closure_set(v___f_328_, 0, v_m_327_);
return v___f_328_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cf___boxed(lean_object* v_D_329_, lean_object* v_G_330_, lean_object* v_NW_331_, lean_object* v_CompW_332_, lean_object* v_inst_333_, lean_object* v_algW_334_, lean_object* v_PtY_335_, lean_object* v_P_336_, lean_object* v_j_337_, lean_object* v_m_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = lp_tree_Formalism_L2_Geo_FormsPkg_cf(v_D_329_, v_G_330_, v_NW_331_, v_CompW_332_, v_inst_333_, v_algW_334_, v_PtY_335_, v_P_336_, v_j_337_, v_m_338_);
lean_dec(v_j_337_);
lean_dec_ref(v_P_336_);
lean_dec_ref(v_algW_334_);
lean_dec(v_inst_333_);
lean_dec_ref(v_NW_331_);
lean_dec_ref(v_G_330_);
lean_dec_ref(v_D_329_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_scal___redArg(lean_object* v_x_340_){
_start:
{
lean_object* v_toFun_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_fst_344_; 
v_toFun_341_ = lean_ctor_get(v_x_340_, 1);
lean_inc(v_toFun_341_);
lean_dec_ref(v_x_340_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_apply_1(v_toFun_341_, v___x_342_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_fst_344_);
lean_dec_ref(v___x_343_);
return v_fst_344_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_scal(lean_object* v_D_345_, lean_object* v_G_346_, lean_object* v_NW_347_, lean_object* v_CompW_348_, lean_object* v_inst_349_, lean_object* v_algW_350_, lean_object* v_PtY_351_, lean_object* v_P_352_, lean_object* v_j_353_, lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lp_tree_Formalism_L2_Geo_FormsPkg_scal___redArg(v_x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_scal___boxed(lean_object* v_D_356_, lean_object* v_G_357_, lean_object* v_NW_358_, lean_object* v_CompW_359_, lean_object* v_inst_360_, lean_object* v_algW_361_, lean_object* v_PtY_362_, lean_object* v_P_363_, lean_object* v_j_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = lp_tree_Formalism_L2_Geo_FormsPkg_scal(v_D_356_, v_G_357_, v_NW_358_, v_CompW_359_, v_inst_360_, v_algW_361_, v_PtY_362_, v_P_363_, v_j_364_, v_x_365_);
lean_dec(v_j_364_);
lean_dec_ref(v_P_363_);
lean_dec_ref(v_algW_361_);
lean_dec(v_inst_360_);
lean_dec_ref(v_NW_358_);
lean_dec_ref(v_G_357_);
lean_dec_ref(v_D_356_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb___redArg(lean_object* v_x_367_){
_start:
{
lean_inc_ref(v_x_367_);
return v_x_367_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb___redArg___boxed(lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = lp_tree_Formalism_L2_Geo_FormsPkg_amb___redArg(v_x_368_);
lean_dec_ref(v_x_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb(lean_object* v_D_370_, lean_object* v_G_371_, lean_object* v_NW_372_, lean_object* v_CompW_373_, lean_object* v_inst_374_, lean_object* v_algW_375_, lean_object* v_PtY_376_, lean_object* v_P_377_, lean_object* v_j_378_, lean_object* v_x_379_){
_start:
{
lean_inc_ref(v_x_379_);
return v_x_379_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_amb___boxed(lean_object* v_D_380_, lean_object* v_G_381_, lean_object* v_NW_382_, lean_object* v_CompW_383_, lean_object* v_inst_384_, lean_object* v_algW_385_, lean_object* v_PtY_386_, lean_object* v_P_387_, lean_object* v_j_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = lp_tree_Formalism_L2_Geo_FormsPkg_amb(v_D_380_, v_G_381_, v_NW_382_, v_CompW_383_, v_inst_384_, v_algW_385_, v_PtY_386_, v_P_387_, v_j_388_, v_x_389_);
lean_dec_ref(v_x_389_);
lean_dec(v_j_388_);
lean_dec_ref(v_P_387_);
lean_dec_ref(v_algW_385_);
lean_dec(v_inst_384_);
lean_dec_ref(v_NW_382_);
lean_dec_ref(v_G_381_);
lean_dec_ref(v_D_380_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cfF___redArg(lean_object* v_m_391_){
_start:
{
lean_object* v___f_392_; 
v___f_392_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg___lam__0), 2, 1);
lean_closure_set(v___f_392_, 0, v_m_391_);
return v___f_392_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cfF(lean_object* v_D_393_, lean_object* v_G_394_, lean_object* v_NW_395_, lean_object* v_CompW_396_, lean_object* v_inst_397_, lean_object* v_algW_398_, lean_object* v_PtY_399_, lean_object* v_P_400_, lean_object* v_j_401_, lean_object* v_m_402_){
_start:
{
lean_object* v___f_403_; 
v___f_403_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_cf___redArg___lam__0), 2, 1);
lean_closure_set(v___f_403_, 0, v_m_402_);
return v___f_403_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_cfF___boxed(lean_object* v_D_404_, lean_object* v_G_405_, lean_object* v_NW_406_, lean_object* v_CompW_407_, lean_object* v_inst_408_, lean_object* v_algW_409_, lean_object* v_PtY_410_, lean_object* v_P_411_, lean_object* v_j_412_, lean_object* v_m_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = lp_tree_Formalism_L2_Geo_FormsPkg_cfF(v_D_404_, v_G_405_, v_NW_406_, v_CompW_407_, v_inst_408_, v_algW_409_, v_PtY_410_, v_P_411_, v_j_412_, v_m_413_);
lean_dec(v_j_412_);
lean_dec_ref(v_P_411_);
lean_dec_ref(v_algW_409_);
lean_dec(v_inst_408_);
lean_dec_ref(v_NW_406_);
lean_dec_ref(v_G_405_);
lean_dec_ref(v_D_404_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_toWeightFamilies___redArg(lean_object* v_D_415_, lean_object* v_G_416_, lean_object* v_NW_417_, lean_object* v_inst_418_, lean_object* v_algW_419_, lean_object* v_P_420_){
_start:
{
lean_object* v_fKO_421_; lean_object* v_eO_422_; lean_object* v_acgC_423_; lean_object* v_modC_424_; lean_object* v_modOC_425_; lean_object* v_supN_426_; lean_object* v_l2NormAlt_427_; lean_object* v_Xc_428_; lean_object* v_acgF_429_; lean_object* v_modF_430_; lean_object* v_sg_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_fKO_421_ = lean_ctor_get(v_P_420_, 0);
lean_inc_ref(v_fKO_421_);
v_eO_422_ = lean_ctor_get(v_P_420_, 1);
lean_inc_ref(v_eO_422_);
v_acgC_423_ = lean_ctor_get(v_P_420_, 3);
lean_inc_ref(v_acgC_423_);
v_modC_424_ = lean_ctor_get(v_P_420_, 4);
lean_inc(v_modC_424_);
v_modOC_425_ = lean_ctor_get(v_P_420_, 5);
lean_inc(v_modOC_425_);
v_supN_426_ = lean_ctor_get(v_P_420_, 8);
lean_inc(v_supN_426_);
v_l2NormAlt_427_ = lean_ctor_get(v_P_420_, 9);
lean_inc(v_l2NormAlt_427_);
v_Xc_428_ = lean_ctor_get(v_P_420_, 10);
lean_inc_ref(v_Xc_428_);
v_acgF_429_ = lean_ctor_get(v_P_420_, 11);
lean_inc_ref(v_acgF_429_);
v_modF_430_ = lean_ctor_get(v_P_420_, 12);
lean_inc(v_modF_430_);
v_sg_431_ = lean_ctor_get(v_P_420_, 13);
lean_inc(v_sg_431_);
v___x_432_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Geo_FormsPkg_Mlat___boxed), 10, 8);
lean_closure_set(v___x_432_, 0, v_D_415_);
lean_closure_set(v___x_432_, 1, v_G_416_);
lean_closure_set(v___x_432_, 2, v_NW_417_);
lean_closure_set(v___x_432_, 3, lean_box(0));
lean_closure_set(v___x_432_, 4, v_inst_418_);
lean_closure_set(v___x_432_, 5, v_algW_419_);
lean_closure_set(v___x_432_, 6, lean_box(0));
lean_closure_set(v___x_432_, 7, v_P_420_);
v___x_433_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_433_, 0, v_fKO_421_);
lean_ctor_set(v___x_433_, 1, v_eO_422_);
lean_ctor_set(v___x_433_, 2, v_acgC_423_);
lean_ctor_set(v___x_433_, 3, v_modC_424_);
lean_ctor_set(v___x_433_, 4, v_modOC_425_);
lean_ctor_set(v___x_433_, 5, v___x_432_);
lean_ctor_set(v___x_433_, 6, v_supN_426_);
lean_ctor_set(v___x_433_, 7, v_l2NormAlt_427_);
lean_ctor_set(v___x_433_, 8, v_Xc_428_);
lean_ctor_set(v___x_433_, 9, v_acgF_429_);
lean_ctor_set(v___x_433_, 10, v_modF_430_);
lean_ctor_set(v___x_433_, 11, v_sg_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_toWeightFamilies(lean_object* v_D_434_, lean_object* v_G_435_, lean_object* v_NW_436_, lean_object* v_CompW_437_, lean_object* v_inst_438_, lean_object* v_algW_439_, lean_object* v_PtY_440_, lean_object* v_P_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lp_tree_Formalism_L2_Geo_FormsPkg_toWeightFamilies___redArg(v_D_434_, v_G_435_, v_NW_436_, v_inst_438_, v_algW_439_, v_P_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_sig0___redArg(lean_object* v_D_443_, lean_object* v_P_444_){
_start:
{
lean_object* v_what_u2082_445_; lean_object* v_embLL_446_; lean_object* v_kL_447_; lean_object* v___f_448_; 
v_what_u2082_445_ = lean_ctor_get(v_D_443_, 4);
lean_inc_ref(v_what_u2082_445_);
lean_dec_ref(v_D_443_);
v_embLL_446_ = lean_ctor_get(v_what_u2082_445_, 1);
lean_inc_ref(v_embLL_446_);
lean_dec_ref(v_what_u2082_445_);
v_kL_447_ = lean_ctor_get(v_P_444_, 2);
lean_inc(v_kL_447_);
lean_dec_ref(v_P_444_);
v___f_448_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_448_, 0, v_kL_447_);
lean_closure_set(v___f_448_, 1, v_embLL_446_);
return v___f_448_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_sig0(lean_object* v_D_449_, lean_object* v_G_450_, lean_object* v_NW_451_, lean_object* v_CompW_452_, lean_object* v_inst_453_, lean_object* v_algW_454_, lean_object* v_PtY_455_, lean_object* v_P_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lp_tree_Formalism_L2_Geo_FormsPkg_sig0___redArg(v_D_449_, v_P_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_FormsPkg_sig0___boxed(lean_object* v_D_458_, lean_object* v_G_459_, lean_object* v_NW_460_, lean_object* v_CompW_461_, lean_object* v_inst_462_, lean_object* v_algW_463_, lean_object* v_PtY_464_, lean_object* v_P_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = lp_tree_Formalism_L2_Geo_FormsPkg_sig0(v_D_458_, v_G_459_, v_NW_460_, v_CompW_461_, v_inst_462_, v_algW_463_, v_PtY_464_, v_P_465_);
lean_dec_ref(v_algW_463_);
lean_dec(v_inst_462_);
lean_dec_ref(v_NW_460_);
lean_dec_ref(v_G_459_);
return v_res_466_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_ArVolEqOfNef(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_InstAddCommSemigroupWt(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_ArVolEqOfNef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
