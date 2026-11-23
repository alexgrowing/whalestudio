// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(lean_object*, lean_object*);
lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_tree_Subsemiring_subtype___at___00GlobalTheory_Mem_Base_OtoLL_spec__4___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_LevCh_host(lean_object*, lean_object*);
static const lean_closure_object lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subsemiring_subtype___at___00GlobalTheory_Mem_Base_OtoLL_spec__4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__1 = (const lean_object*)&lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_5_ == 0)
{
size_t v___x_6_; size_t v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_6_ = ((size_t)1ULL);
v___x_7_ = lean_usize_sub(v_i_2_, v___x_6_);
v___x_8_ = lean_array_uget_borrowed(v_as_1_, v___x_7_);
v___x_9_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(v___x_8_, v_b_4_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_inc(v___x_8_);
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v_b_4_);
v_i_2_ = v___x_7_;
v_b_4_ = v___x_10_;
goto _start;
}
else
{
v_i_2_ = v___x_7_;
goto _start;
}
}
else
{
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0_spec__1___boxed(lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_, lean_object* v_b_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; lean_object* v_res_19_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_19_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0_spec__1(v_as_13_, v_i_boxed_17_, v_stop_boxed_18_, v_b_16_);
lean_dec_ref(v_as_13_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0(lean_object* v_init_20_, lean_object* v_l_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_22_ = lean_array_mk(v_l_21_);
v___x_23_ = lean_array_get_size(v___x_22_);
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_nat_dec_lt(v___x_24_, v___x_23_);
if (v___x_25_ == 0)
{
lean_dec_ref(v___x_22_);
return v_init_20_;
}
else
{
size_t v___x_26_; size_t v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_usize_of_nat(v___x_23_);
v___x_27_ = ((size_t)0ULL);
v___x_28_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0_spec__1(v___x_22_, v___x_26_, v___x_27_, v_init_20_);
lean_dec_ref(v___x_22_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0(lean_object* v_s_29_, lean_object* v_t_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0(v_t_30_, v_s_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_LevCh_host(lean_object* v_P_32_, lean_object* v_L_33_){
_start:
{
lean_object* v_H_34_; lean_object* v_wordFin_35_; lean_object* v_toHostAx_36_; lean_object* v_sqq_37_; lean_object* v_splitBound_38_; lean_object* v_00_u03c6_u2080_39_; lean_object* v_00_U0001d51f_40_; lean_object* v_levelPrimes_41_; lean_object* v_g_42_; lean_object* v_pde_43_; lean_object* v_pde_x27_44_; lean_object* v_ccK_45_; lean_object* v_TT_46_; lean_object* v_T2_47_; lean_object* v_u0_48_; lean_object* v_Lw_49_; lean_object* v_CT2_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_60_; 
v_H_34_ = lean_ctor_get(v_P_32_, 1);
lean_inc_ref(v_H_34_);
v_wordFin_35_ = lean_ctor_get(v_P_32_, 2);
lean_inc(v_wordFin_35_);
lean_dec_ref(v_P_32_);
v_toHostAx_36_ = lean_ctor_get(v_H_34_, 0);
v_sqq_37_ = lean_ctor_get(v_H_34_, 1);
v_splitBound_38_ = lean_ctor_get(v_H_34_, 2);
v_00_u03c6_u2080_39_ = lean_ctor_get(v_H_34_, 3);
v_00_U0001d51f_40_ = lean_ctor_get(v_H_34_, 4);
v_levelPrimes_41_ = lean_ctor_get(v_H_34_, 5);
v_g_42_ = lean_ctor_get(v_H_34_, 6);
v_pde_43_ = lean_ctor_get(v_H_34_, 7);
v_pde_x27_44_ = lean_ctor_get(v_H_34_, 8);
v_ccK_45_ = lean_ctor_get(v_H_34_, 9);
v_TT_46_ = lean_ctor_get(v_H_34_, 10);
v_T2_47_ = lean_ctor_get(v_H_34_, 11);
v_u0_48_ = lean_ctor_get(v_H_34_, 12);
v_Lw_49_ = lean_ctor_get(v_H_34_, 13);
v_CT2_50_ = lean_ctor_get(v_H_34_, 14);
v_isSharedCheck_60_ = !lean_is_exclusive(v_H_34_);
if (v_isSharedCheck_60_ == 0)
{
v___x_52_ = v_H_34_;
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_CT2_50_);
lean_inc(v_Lw_49_);
lean_inc(v_u0_48_);
lean_inc(v_T2_47_);
lean_inc(v_TT_46_);
lean_inc(v_ccK_45_);
lean_inc(v_pde_x27_44_);
lean_inc(v_pde_43_);
lean_inc(v_g_42_);
lean_inc(v_levelPrimes_41_);
lean_inc(v_00_U0001d51f_40_);
lean_inc(v_00_u03c6_u2080_39_);
lean_inc(v_splitBound_38_);
lean_inc(v_sqq_37_);
lean_inc(v_toHostAx_36_);
lean_dec(v_H_34_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_T_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v_T_54_ = lean_ctor_get(v_L_33_, 0);
lean_inc_ref(v_T_54_);
lean_dec_ref(v_L_33_);
v___x_55_ = lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(v_T_54_, v_wordFin_35_);
v___x_56_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00GlobalTheory_Mem_LevCh_host_spec__0_spec__0(v___x_55_, v_levelPrimes_41_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 5, v___x_56_);
v___x_58_ = v___x_52_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_toHostAx_36_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_sqq_37_);
lean_ctor_set(v_reuseFailAlloc_59_, 2, v_splitBound_38_);
lean_ctor_set(v_reuseFailAlloc_59_, 3, v_00_u03c6_u2080_39_);
lean_ctor_set(v_reuseFailAlloc_59_, 4, v_00_U0001d51f_40_);
lean_ctor_set(v_reuseFailAlloc_59_, 5, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_59_, 6, v_g_42_);
lean_ctor_set(v_reuseFailAlloc_59_, 7, v_pde_43_);
lean_ctor_set(v_reuseFailAlloc_59_, 8, v_pde_x27_44_);
lean_ctor_set(v_reuseFailAlloc_59_, 9, v_ccK_45_);
lean_ctor_set(v_reuseFailAlloc_59_, 10, v_TT_46_);
lean_ctor_set(v_reuseFailAlloc_59_, 11, v_T2_47_);
lean_ctor_set(v_reuseFailAlloc_59_, 12, v_u0_48_);
lean_ctor_set(v_reuseFailAlloc_59_, 13, v_Lw_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 14, v_CT2_50_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0(lean_object* v_H_63_, lean_object* v_piT_64_, lean_object* v_u_u2080_65_, lean_object* v_u_66_){
_start:
{
lean_object* v_toHostAx_67_; lean_object* v_instField_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_toDiv_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_toHostAx_67_ = lean_ctor_get(v_H_63_, 0);
lean_inc_ref(v_toHostAx_67_);
lean_dec_ref(v_H_63_);
v_instField_68_ = lean_ctor_get(v_toHostAx_67_, 3);
lean_inc_ref(v_instField_68_);
lean_dec_ref(v_toHostAx_67_);
v___x_69_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_68_);
v___x_70_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_69_);
lean_dec_ref(v___x_69_);
v_toDiv_71_ = lean_ctor_get(v___x_70_, 2);
lean_inc(v_toDiv_71_);
lean_dec_ref(v___x_70_);
lean_inc(v_piT_64_);
v___x_72_ = lean_apply_1(v_piT_64_, v_u_u2080_65_);
v___f_73_ = ((lean_object*)(lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__0));
v___f_74_ = ((lean_object*)(lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0___closed__1));
v___x_75_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_74_, v___f_73_, v___x_72_);
v___x_76_ = lean_apply_1(v_piT_64_, v_u_66_);
v___x_77_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_74_, v___f_73_, v___x_76_);
v___x_78_ = lean_apply_2(v_toDiv_71_, v___x_75_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg(lean_object* v_P_79_, lean_object* v_L_80_, lean_object* v_sp_81_){
_start:
{
lean_object* v_R_82_; lean_object* v_H_83_; lean_object* v_wordFin_84_; lean_object* v_u_u2080_85_; lean_object* v_hcW_86_; lean_object* v_T_87_; lean_object* v_piT_88_; lean_object* v_duStar_89_; lean_object* v_Dstar_90_; lean_object* v_GamP_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_R_82_ = lean_ctor_get(v_P_79_, 0);
lean_inc_ref(v_R_82_);
v_H_83_ = lean_ctor_get(v_P_79_, 1);
v_wordFin_84_ = lean_ctor_get(v_P_79_, 2);
lean_inc(v_wordFin_84_);
v_u_u2080_85_ = lean_ctor_get(v_P_79_, 3);
lean_inc_n(v_u_u2080_85_, 3);
v_hcW_86_ = lean_ctor_get(v_P_79_, 4);
lean_inc_ref_n(v_hcW_86_, 2);
v_T_87_ = lean_ctor_get(v_L_80_, 0);
lean_inc_ref(v_T_87_);
v_piT_88_ = lean_ctor_get(v_L_80_, 1);
v_duStar_89_ = lean_ctor_get(v_L_80_, 2);
lean_inc_ref(v_duStar_89_);
v_Dstar_90_ = lean_ctor_get(v_L_80_, 3);
lean_inc(v_Dstar_90_);
v_GamP_91_ = lean_ctor_get(v_L_80_, 4);
lean_inc(v_GamP_91_);
lean_inc(v_piT_88_);
lean_inc_ref(v_H_83_);
v___f_92_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg___lam__0), 4, 3);
lean_closure_set(v___f_92_, 0, v_H_83_);
lean_closure_set(v___f_92_, 1, v_piT_88_);
lean_closure_set(v___f_92_, 2, v_u_u2080_85_);
v___x_93_ = lp_tree_GlobalTheory_Mem_LevCh_host(v_P_79_, v_L_80_);
v___x_94_ = lean_apply_1(v_hcW_86_, v_u_u2080_85_);
v___x_95_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_95_, 0, v_R_82_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
lean_ctor_set(v___x_95_, 2, v_sp_81_);
lean_ctor_set(v___x_95_, 3, v_wordFin_84_);
lean_ctor_set(v___x_95_, 4, v_u_u2080_85_);
lean_ctor_set(v___x_95_, 5, v___x_94_);
lean_ctor_set(v___x_95_, 6, v_hcW_86_);
lean_ctor_set(v___x_95_, 7, v_T_87_);
lean_ctor_set(v___x_95_, 8, v___f_92_);
lean_ctor_set(v___x_95_, 9, v_duStar_89_);
lean_ctor_set(v___x_95_, 10, v_Dstar_90_);
lean_ctor_set(v___x_95_, 11, v_GamP_91_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Pre_ofCh(lean_object* v_P_96_, lean_object* v_L_97_, lean_object* v_sp_98_, lean_object* v_hT_99_, lean_object* v_hY_100_, lean_object* v_hA_101_, lean_object* v_hV_102_, lean_object* v_hz_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_tree_GlobalTheory_Mem_Pre_ofCh___redArg(v_P_96_, v_L_97_, v_sp_98_);
return v___x_104_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_Foundations_RootOfUnityEightQMemCoeffGaloisSubfield(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_DuStarPos(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_Foundations_RootOfUnityEightQMemCoeffGaloisSubfield(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
