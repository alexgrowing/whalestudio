// Lean compiler output
// Module: Formalism.IncomingBounds.StatementThmP
// Imports: public import Init public meta import Init public import Formalism.IncomingBounds.IncomingBound
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_Finsupp_prod___at___00Nat_floorRoot_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_IncomingBounds_mfact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_IncomingBounds_mfact___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_IncomingBounds_mfact___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_jetAt0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_jetAt0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_jetAt0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degL___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degL___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degR___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degR___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg___lam__0(lean_object* v_x_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lp_mathlib_Nat_factorialBinarySplitting(v_k_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg___lam__0___boxed(lean_object* v_x_4_, lean_object* v_k_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_IncomingBounds_mfact___redArg___lam__0(v_x_4_, v_k_5_);
lean_dec(v_k_5_);
lean_dec(v_x_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact___redArg(lean_object* v_m_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; 
v___f_9_ = ((lean_object*)(lp_tree_Formalism_IncomingBounds_mfact___redArg___closed__0));
v___x_10_ = lp_mathlib_Finsupp_prod___at___00Nat_floorRoot_spec__0___redArg(v_m_8_, v___f_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_mfact(lean_object* v_00_u03c3_11_, lean_object* v_m_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_tree_Formalism_IncomingBounds_mfact___redArg(v_m_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_jetAt0___redArg___lam__0(lean_object* v_P_14_, lean_object* v_toNatCast_15_, lean_object* v_toMul_16_, lean_object* v_g_17_, lean_object* v_m_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc_ref_n(v_m_18_, 2);
v___x_19_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_18_, v_P_14_);
v___x_20_ = lp_tree_Formalism_IncomingBounds_mfact___redArg(v_m_18_);
v___x_21_ = lean_apply_1(v_toNatCast_15_, v___x_20_);
lean_inc(v_toMul_16_);
v___x_22_ = lean_apply_2(v_toMul_16_, v___x_19_, v___x_21_);
v___x_23_ = lean_apply_1(v_g_17_, v_m_18_);
v___x_24_ = lean_apply_2(v_toMul_16_, v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_jetAt0___redArg(lean_object* v_inst_25_, lean_object* v_P_26_, lean_object* v_g_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_toSemiring_30_; lean_object* v_toAddCommMonoid_31_; lean_object* v_support_32_; lean_object* v___x_33_; lean_object* v_toMul_34_; lean_object* v___x_35_; lean_object* v_toRing_36_; lean_object* v___x_37_; lean_object* v_toAddMonoidWithOne_38_; lean_object* v_toNatCast_39_; lean_object* v___f_40_; lean_object* v___x_41_; 
v___x_28_ = lp_mathlib_Field_toSemifield___redArg(v_inst_25_);
v___x_29_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_28_);
v_toSemiring_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref(v_toSemiring_30_);
lean_dec_ref(v___x_29_);
v_toAddCommMonoid_31_ = lean_ctor_get(v_toSemiring_30_, 0);
lean_inc_ref(v_toAddCommMonoid_31_);
v_support_32_ = lean_ctor_get(v_P_26_, 0);
lean_inc(v_support_32_);
v___x_33_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_30_);
v_toMul_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_toMul_34_);
lean_dec_ref(v___x_33_);
v___x_35_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_25_);
v_toRing_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_toRing_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_36_);
v_toAddMonoidWithOne_38_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_toAddMonoidWithOne_38_);
lean_dec_ref(v___x_37_);
v_toNatCast_39_ = lean_ctor_get(v_toAddMonoidWithOne_38_, 0);
lean_inc(v_toNatCast_39_);
lean_dec_ref(v_toAddMonoidWithOne_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_jetAt0___redArg___lam__0), 5, 4);
lean_closure_set(v___f_40_, 0, v_P_26_);
lean_closure_set(v___f_40_, 1, v_toNatCast_39_);
lean_closure_set(v___f_40_, 2, v_toMul_34_);
lean_closure_set(v___f_40_, 3, v_g_27_);
v___x_41_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_31_, v_support_32_, v___f_40_);
lean_dec_ref(v_toAddCommMonoid_31_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_jetAt0(lean_object* v_C_42_, lean_object* v_inst_43_, lean_object* v_00_u03c3_44_, lean_object* v_P_45_, lean_object* v_g_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_IncomingBounds_jetAt0___redArg(v_inst_43_, v_P_45_, v_g_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE___lam__0(lean_object* v_l_48_, lean_object* v___x_49_, lean_object* v_t_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_nat_pow(v_l_48_, v___x_49_);
v___x_52_ = lean_nat_pow(v___x_51_, v_t_50_);
lean_dec(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE___lam__0___boxed(lean_object* v_l_53_, lean_object* v___x_54_, lean_object* v_t_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_Formalism_IncomingBounds_expE___lam__0(v_l_53_, v___x_54_, v_t_55_);
lean_dec(v_t_55_);
lean_dec(v___x_54_);
lean_dec(v_l_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE(lean_object* v_l_57_, lean_object* v_i_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_sub(v_i_58_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(2u);
lean_inc(v_l_57_);
v___f_62_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_expE___lam__0___boxed), 3, 2);
lean_closure_set(v___f_62_, 0, v_l_57_);
lean_closure_set(v___f_62_, 1, v___x_61_);
v___x_63_ = lean_nat_shiftr(v___x_60_, v___x_59_);
lean_dec(v___x_60_);
v___x_64_ = l_List_range(v___x_63_);
v___x_65_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_64_, v___f_62_);
v___x_66_ = lean_nat_mul(v_l_57_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v_l_57_);
v___x_67_ = lean_nat_add(v___x_59_, v___x_66_);
lean_dec(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_expE___boxed(lean_object* v_l_68_, lean_object* v_i_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_IncomingBounds_expE(v_l_68_, v_i_69_);
lean_dec(v_i_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degL___lam__0(lean_object* v_m_71_, lean_object* v_b_72_, lean_object* v_c_73_){
_start:
{
lean_object* v_toFun_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_83_; 
v_toFun_74_ = lean_ctor_get(v_m_71_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_m_71_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v_m_71_, 0);
lean_dec(v_unused_84_);
v___x_76_ = v_m_71_;
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_toFun_74_);
lean_dec(v_m_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v_c_73_);
lean_ctor_set(v___x_76_, 0, v_b_72_);
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_b_72_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_c_73_);
v___x_79_ = v_reuseFailAlloc_82_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
v___x_81_ = lean_apply_1(v_toFun_74_, v___x_80_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degL___lam__1(lean_object* v_m_85_, lean_object* v___x_86_, lean_object* v_b_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; 
v___f_88_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_degL___lam__0), 3, 2);
lean_closure_set(v___f_88_, 0, v_m_85_);
lean_closure_set(v___f_88_, 1, v_b_87_);
v___x_89_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_86_, v___f_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degL(lean_object* v_n0_90_, lean_object* v_m_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___x_94_; 
v___x_92_ = l_List_finRange(v_n0_90_);
lean_inc(v___x_92_);
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_degL___lam__1), 3, 2);
lean_closure_set(v___f_93_, 0, v_m_91_);
lean_closure_set(v___f_93_, 1, v___x_92_);
v___x_94_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_92_, v___f_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degR___lam__0(lean_object* v_m_95_, lean_object* v_b_96_, lean_object* v_c_97_){
_start:
{
lean_object* v_toFun_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_toFun_98_ = lean_ctor_get(v_m_95_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_m_95_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_m_95_, 0);
lean_dec(v_unused_108_);
v___x_100_ = v_m_95_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_toFun_98_);
lean_dec(v_m_95_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v_c_97_);
lean_ctor_set(v___x_100_, 0, v_b_96_);
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_b_96_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_c_97_);
v___x_103_ = v_reuseFailAlloc_106_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___x_105_ = lean_apply_1(v_toFun_98_, v___x_104_);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degR___lam__1(lean_object* v_m_109_, lean_object* v___x_110_, lean_object* v_b_111_){
_start:
{
lean_object* v___f_112_; lean_object* v___x_113_; 
v___f_112_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_degR___lam__0), 3, 2);
lean_closure_set(v___f_112_, 0, v_m_109_);
lean_closure_set(v___f_112_, 1, v_b_111_);
v___x_113_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_110_, v___f_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IncomingBounds_degR(lean_object* v_n0_114_, lean_object* v_m_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___f_117_; lean_object* v___x_118_; 
v___x_116_ = l_List_finRange(v_n0_114_);
lean_inc(v___x_116_);
v___f_117_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_degR___lam__1), 3, 2);
lean_closure_set(v___f_117_, 0, v_m_115_);
lean_closure_set(v___f_117_, 1, v___x_116_);
v___x_118_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_116_, v___f_117_);
return v___x_118_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_IncomingBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_IncomingBounds_StatementThmP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_IncomingBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
