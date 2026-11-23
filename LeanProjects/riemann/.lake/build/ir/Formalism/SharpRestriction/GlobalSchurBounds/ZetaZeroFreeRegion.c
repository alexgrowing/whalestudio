// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion public import Formalism.SharpRestriction.ParConsts
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
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
extern lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0;
lean_object* lp_tree_Formalism_HC_Frame_dig(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_tau2___redArg(lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_chQ(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_chC(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_chC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_chC___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_psC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_psC___boxed(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__0_value;
static const lean_closure_object lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__1 = (const lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__1_value;
static const lean_closure_object lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__1_value)} };
static const lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__2 = (const lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__2_value;
static const lean_closure_object lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__3___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__2_value),((lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__0_value)} };
static const lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__3 = (const lean_object*)&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__3_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Complex_commRing;
v___x_2_ = lp_mathlib_Ring_toNonAssocRing___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__0, &lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__0_once, _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__0);
v___x_4_ = lp_mathlib_Int_castRingHom___redArg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___f_6_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__1, &lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__1_once, _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__1);
v___f_6_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
return v___f_6_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC(void){
_start:
{
lean_object* v___f_7_; 
v___f_7_ = lean_obj_once(&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__2, &lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__2_once, _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC___closed__2);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_chC(lean_object* v_D_8_){
_start:
{
lean_object* v_R_9_; lean_object* v_toFrame_10_; lean_object* v___x_11_; 
v_R_9_ = lean_ctor_get(v_D_8_, 0);
v_toFrame_10_ = lean_ctor_get(v_R_9_, 0);
v___x_11_ = lp_tree_Formalism_HC_Frame_chC(v_toFrame_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_chC___boxed(lean_object* v_D_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_chC(v_D_12_);
lean_dec_ref(v_D_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_psC(lean_object* v_D_14_){
_start:
{
lean_object* v_R_15_; lean_object* v_toFrame_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___f_19_; 
v_R_15_ = lean_ctor_get(v_D_14_, 0);
v_toFrame_16_ = lean_ctor_get(v_R_15_, 0);
v___x_17_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC;
v___x_18_ = lp_tree_Formalism_HC_Frame_chQ(v_toFrame_16_);
v___f_19_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v___x_18_);
lean_closure_set(v___f_19_, 1, v___x_17_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_psC___boxed(lean_object* v_D_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_psC(v_D_20_);
lean_dec_ref(v_D_20_);
return v_res_21_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___closed__0(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner(lean_object* v_D_23_){
_start:
{
lean_object* v_R_24_; lean_object* v_toFrame_25_; lean_object* v_grp_26_; lean_object* v___x_27_; lean_object* v_toZero_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_39_; 
v_R_24_ = lean_ctor_get(v_D_23_, 0);
v_toFrame_25_ = lean_ctor_get(v_R_24_, 0);
v_grp_26_ = lean_ctor_get(v_toFrame_25_, 2);
v___x_27_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_grp_26_);
v_toZero_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v___x_27_, 1);
lean_dec(v_unused_40_);
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_39_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_toZero_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_39_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v_toFun_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_32_ = lean_obj_once(&lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___closed__0, &lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___closed__0_once, _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___closed__0);
v_toFun_33_ = lean_ctor_get(v___x_32_, 0);
v___x_34_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0;
lean_inc(v_toFun_33_);
v___x_35_ = lean_apply_1(v_toFun_33_, v_toZero_28_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_35_);
lean_ctor_set(v___x_30_, 0, v___x_34_);
v___x_37_ = v___x_30_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner___boxed(lean_object* v_D_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_iner(v_D_41_);
lean_dec_ref(v_D_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__0(lean_object* v_R_43_, lean_object* v_u0_44_, lean_object* v_s_45_){
_start:
{
lean_object* v_toFrame_46_; lean_object* v_grp_47_; lean_object* v_toAddMonoid_48_; lean_object* v_toAddSemigroup_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_toFrame_46_ = lean_ctor_get(v_R_43_, 0);
lean_inc_ref(v_toFrame_46_);
lean_dec_ref(v_R_43_);
v_grp_47_ = lean_ctor_get(v_toFrame_46_, 2);
v_toAddMonoid_48_ = lean_ctor_get(v_grp_47_, 0);
v_toAddSemigroup_49_ = lean_ctor_get(v_toAddMonoid_48_, 0);
lean_inc(v_toAddSemigroup_49_);
v___x_50_ = lp_tree_Formalism_HC_Frame_dig(v_toFrame_46_, v_s_45_);
v___x_51_ = lean_apply_2(v_toAddSemigroup_49_, v___x_50_, v_u0_44_);
v___x_52_ = lp_tree_Formalism_HC_Frame_tau2___redArg(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__1(lean_object* v_a_53_, lean_object* v_b_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_56_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_55_, v_a_53_, v_b_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__1___boxed(lean_object* v_a_57_, lean_object* v_b_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__1(v_a_57_, v_b_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__2(lean_object* v___f_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
uint8_t v___x_64_; 
lean_inc_ref(v___f_61_);
v___x_64_ = l_instDecidableEqProd___redArg(v___f_61_, v___f_61_, v_a_62_, v_b_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__2___boxed(lean_object* v___f_65_, lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__2(v___f_65_, v_a_66_, v_b_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__3(lean_object* v___f_70_, lean_object* v___f_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_instDecidableEqProd___redArg(v___f_70_, v___f_71_, v_a_72_, v_b_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__3___boxed(lean_object* v___f_75_, lean_object* v___f_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__3(v___f_75_, v___f_76_, v_a_77_, v_b_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt(lean_object* v_D_88_, lean_object* v_u0_89_){
_start:
{
lean_object* v_host_90_; lean_object* v_R_91_; lean_object* v_T2_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v_host_90_ = lean_ctor_get(v_D_88_, 1);
lean_inc_ref(v_host_90_);
v_R_91_ = lean_ctor_get(v_D_88_, 0);
lean_inc_ref(v_R_91_);
lean_dec_ref(v_D_88_);
v_T2_92_ = lean_ctor_get(v_host_90_, 11);
lean_inc(v_T2_92_);
lean_dec_ref(v_host_90_);
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___lam__0), 3, 2);
lean_closure_set(v___f_93_, 0, v_R_91_);
lean_closure_set(v___f_93_, 1, v_u0_89_);
v___f_94_ = ((lean_object*)(lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_thickAt___closed__3));
v___x_95_ = lp_mathlib_Finset_image___redArg(v___f_94_, v___f_93_, v_T2_92_);
return v___x_95_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FiltrationBoundaryCriterion(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FiltrationCocycleLiftCriterion(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_ZetaZeroFreeRegion(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FiltrationBoundaryCriterion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FiltrationCocycleLiftCriterion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC = _init_lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC();
lean_mark_persistent(lp_tree_Formalism_MainNotions_ZetaZeroFreeRegion_sgnC);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
