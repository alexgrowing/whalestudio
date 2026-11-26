// Lean compiler output
// Module: New.Congruences.Lifting.CupProductBound
// Imports: public import Init public meta import Init public import New.Congruences.Lifting.HodgeExpansion
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_LinearMap_snd___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__1;
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_snd___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0);
v___x_4_ = lean_int_neg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__1, &lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__1);
v___x_7_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0(lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__2, &lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__2_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__2);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0(v_x_10_);
lean_dec(v_x_10_);
return v_res_11_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__0___closed__0);
v___x_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1(lean_object* v_x_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___closed__0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1___boxed(lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__1(v_x_17_);
lean_dec_ref(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__2(lean_object* v_x_19_, lean_object* v___y_20_){
_start:
{
lean_inc(v___y_20_);
return v___y_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__2___boxed(lean_object* v_x_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___lam__2(v_x_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec(v_x_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg(lean_object* v_S_27_){
_start:
{
lean_object* v_paramLattice_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_49_; 
v_paramLattice_28_ = lean_ctor_get(v_S_27_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_S_27_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; lean_object* v_unused_51_; 
v_unused_50_ = lean_ctor_get(v_S_27_, 2);
lean_dec(v_unused_50_);
v_unused_51_ = lean_ctor_get(v_S_27_, 0);
lean_dec(v_unused_51_);
v___x_30_ = v_S_27_;
v_isShared_31_ = v_isSharedCheck_49_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_paramLattice_28_);
lean_dec(v_S_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_49_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_addCommGroup_32_; lean_object* v_moduleO_33_; lean_object* v_moduleZp_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_47_; 
v_addCommGroup_32_ = lean_ctor_get(v_paramLattice_28_, 0);
v_moduleO_33_ = lean_ctor_get(v_paramLattice_28_, 1);
v_moduleZp_34_ = lean_ctor_get(v_paramLattice_28_, 2);
v_isSharedCheck_47_ = !lean_is_exclusive(v_paramLattice_28_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v_paramLattice_28_, 3);
lean_dec(v_unused_48_);
v___x_36_ = v_paramLattice_28_;
v_isShared_37_ = v_isSharedCheck_47_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_moduleZp_34_);
lean_inc(v_moduleO_33_);
lean_inc(v_addCommGroup_32_);
lean_dec(v_paramLattice_28_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_47_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_42_; 
v___f_38_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__0));
v___f_39_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__1));
v___f_40_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__2));
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 3, v___f_40_);
v___x_42_ = v___x_36_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_addCommGroup_32_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_moduleO_33_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v_moduleZp_34_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v___f_40_);
v___x_42_ = v_reuseFailAlloc_46_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_44_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 2, v___f_38_);
lean_ctor_set(v___x_30_, 1, v___f_39_);
lean_ctor_set(v___x_30_, 0, v___x_42_);
v___x_44_ = v___x_30_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___f_39_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v___f_38_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice(lean_object* v_p_52_, lean_object* v_inst_53_, lean_object* v_00_u0393_54_, lean_object* v_k_55_, lean_object* v_O_56_, lean_object* v_S_57_){
_start:
{
lean_object* v_paramLattice_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_79_; 
v_paramLattice_58_ = lean_ctor_get(v_S_57_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_S_57_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; lean_object* v_unused_81_; 
v_unused_80_ = lean_ctor_get(v_S_57_, 2);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v_S_57_, 0);
lean_dec(v_unused_81_);
v___x_60_ = v_S_57_;
v_isShared_61_ = v_isSharedCheck_79_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_paramLattice_58_);
lean_dec(v_S_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_79_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_addCommGroup_62_; lean_object* v_moduleO_63_; lean_object* v_moduleZp_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v_addCommGroup_62_ = lean_ctor_get(v_paramLattice_58_, 0);
v_moduleO_63_ = lean_ctor_get(v_paramLattice_58_, 1);
v_moduleZp_64_ = lean_ctor_get(v_paramLattice_58_, 2);
v_isSharedCheck_77_ = !lean_is_exclusive(v_paramLattice_58_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; 
v_unused_78_ = lean_ctor_get(v_paramLattice_58_, 3);
lean_dec(v_unused_78_);
v___x_66_ = v_paramLattice_58_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_moduleZp_64_);
lean_inc(v_moduleO_63_);
lean_inc(v_addCommGroup_62_);
lean_dec(v_paramLattice_58_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___x_72_; 
v___f_68_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__0));
v___f_69_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__1));
v___f_70_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___redArg___closed__2));
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 3, v___f_70_);
v___x_72_ = v___x_66_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_addCommGroup_62_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_moduleO_63_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v_moduleZp_64_);
lean_ctor_set(v_reuseFailAlloc_76_, 3, v___f_70_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 2, v___f_68_);
lean_ctor_set(v___x_60_, 1, v___f_69_);
lean_ctor_set(v___x_60_, 0, v___x_72_);
v___x_74_ = v___x_60_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___f_69_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v___f_68_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice___boxed(lean_object* v_p_82_, lean_object* v_inst_83_, lean_object* v_00_u0393_84_, lean_object* v_k_85_, lean_object* v_O_86_, lean_object* v_S_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_GRH_New_Lift_KummerChart_PairingSide_trivialLattice(v_p_82_, v_inst_83_, v_00_u0393_84_, v_k_85_, v_O_86_, v_S_87_);
lean_dec_ref(v_O_86_);
lean_dec_ref(v_k_85_);
lean_dec_ref(v_00_u0393_84_);
lean_dec(v_p_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg(){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___closed__0));
return v___f_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___boxed(lean_object* v___dummy_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg();
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial(lean_object* v_p_94_, lean_object* v_inst_95_, lean_object* v_00_u0393_96_, lean_object* v_k_97_, lean_object* v_O_98_, lean_object* v_S_99_){
_start:
{
lean_object* v___f_100_; 
v___f_100_ = ((lean_object*)(lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___redArg___closed__0));
return v___f_100_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial___boxed(lean_object* v_p_101_, lean_object* v_inst_102_, lean_object* v_00_u0393_103_, lean_object* v_k_104_, lean_object* v_O_105_, lean_object* v_S_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_GRH_New_Lift_KummerChart_PairingSide_projTrivial(v_p_101_, v_inst_102_, v_00_u0393_103_, v_k_104_, v_O_105_, v_S_106_);
lean_dec_ref(v_S_106_);
lean_dec_ref(v_O_105_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_00_u0393_103_);
lean_dec(v_p_101_);
return v_res_107_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_HodgeExpansion(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_CupProductBound(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_Lifting_HodgeExpansion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
