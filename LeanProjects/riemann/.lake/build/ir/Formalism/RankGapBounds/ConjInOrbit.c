// Lean compiler output
// Module: Formalism.RankGapBounds.ConjInOrbit
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0;
static lean_once_cell_t lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1;
static lean_once_cell_t lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__2;
static lean_once_cell_t lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg;
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_c0;
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_cc(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_cc___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_place(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_place___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_ZMod_instField___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0);
v___x_4_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__0);
v___x_6_ = lp_mathlib_Field_toSemifield___redArg(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__2, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__2_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__2);
v___x_8_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg(void){
_start:
{
lean_object* v___x_9_; lean_object* v_toRing_10_; lean_object* v___x_11_; lean_object* v_toAddMonoidWithOne_12_; lean_object* v_toOne_13_; lean_object* v___x_14_; lean_object* v_toSemiring_15_; lean_object* v___x_16_; lean_object* v_toZero_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v___x_9_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1);
v_toRing_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toRing_10_);
v___x_11_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_10_);
v_toAddMonoidWithOne_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc_ref(v_toAddMonoidWithOne_12_);
lean_dec_ref(v___x_11_);
v_toOne_13_ = lean_ctor_get(v_toAddMonoidWithOne_12_, 2);
lean_inc(v_toOne_13_);
lean_dec_ref(v_toAddMonoidWithOne_12_);
v___x_14_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3);
v_toSemiring_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toSemiring_15_);
v___x_16_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_15_);
v_toZero_17_ = lean_ctor_get(v___x_16_, 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_16_, 0);
lean_dec(v_unused_25_);
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_toZero_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v_toOne_13_);
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_toOne_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_toZero_17_);
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
static lean_object* _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_c0(void){
_start:
{
lean_object* v___x_26_; lean_object* v_toSemiring_27_; lean_object* v___x_28_; lean_object* v_toZero_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_41_; 
v___x_26_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3);
v_toSemiring_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc_ref(v_toSemiring_27_);
v___x_28_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_27_);
v_toZero_29_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_41_ == 0)
{
lean_object* v_unused_42_; 
v_unused_42_ = lean_ctor_get(v___x_28_, 0);
lean_dec(v_unused_42_);
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_41_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_toZero_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_41_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v_toRing_34_; lean_object* v___x_35_; lean_object* v_toAddMonoidWithOne_36_; lean_object* v_toOne_37_; lean_object* v___x_39_; 
v___x_33_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__1);
v_toRing_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc_ref(v_toRing_34_);
v___x_35_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_34_);
v_toAddMonoidWithOne_36_ = lean_ctor_get(v___x_35_, 1);
lean_inc_ref(v_toAddMonoidWithOne_36_);
lean_dec_ref(v___x_35_);
v_toOne_37_ = lean_ctor_get(v_toAddMonoidWithOne_36_, 2);
lean_inc(v_toOne_37_);
lean_dec_ref(v_toAddMonoidWithOne_36_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v_toOne_37_);
lean_ctor_set(v___x_31_, 0, v_toZero_29_);
v___x_39_ = v___x_31_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_toZero_29_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_toOne_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_cc(lean_object* v_e_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toSemiring_47_; lean_object* v___x_48_; lean_object* v_toZero_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
v___x_44_ = lean_unsigned_to_nat(2u);
v___x_45_ = lean_nat_pow(v___x_44_, v_e_43_);
v___x_46_ = lp_mathlib_ZMod_commRing(v___x_45_);
v_toSemiring_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_toSemiring_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_47_);
v_toZero_49_ = lean_ctor_get(v___x_48_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v___x_48_, 0);
lean_dec(v_unused_58_);
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_toZero_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_c0;
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_53_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_toZero_49_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_cc___boxed(lean_object* v_e_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_cc(v_e_59_);
lean_dec(v_e_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_place(lean_object* v_e_61_, lean_object* v_00_u03b3_62_){
_start:
{
lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v_fst_65_; lean_object* v_snd_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toSemiring_69_; lean_object* v___x_70_; lean_object* v_toZero_71_; uint8_t v___x_72_; 
v_fst_63_ = lean_ctor_get(v_00_u03b3_62_, 0);
v_snd_64_ = lean_ctor_get(v_00_u03b3_62_, 1);
v_fst_65_ = lean_ctor_get(v_fst_63_, 0);
v_snd_66_ = lean_ctor_get(v_fst_63_, 1);
v___x_67_ = lean_unsigned_to_nat(2u);
v___x_68_ = lean_obj_once(&lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3, &lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3_once, _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg___closed__3);
v_toSemiring_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_toSemiring_69_);
v___x_70_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_69_);
v_toZero_71_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_toZero_71_);
lean_dec_ref(v___x_70_);
v___x_72_ = lp_mathlib_ZMod_decidableEq(v___x_67_, v_snd_66_, v_toZero_71_);
lean_dec(v_toZero_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v_toAdd_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_toSemiring_77_; lean_object* v___x_78_; lean_object* v_toAdd_79_; lean_object* v___x_80_; lean_object* v_fst_81_; lean_object* v_snd_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_101_; 
lean_inc(v_snd_66_);
lean_inc(v_fst_65_);
lean_inc(v_snd_64_);
lean_dec_ref(v_00_u03b3_62_);
lean_inc_ref(v_toSemiring_69_);
v___x_73_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_69_);
v_toAdd_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_toAdd_74_);
lean_dec_ref(v___x_73_);
v___x_75_ = lean_nat_pow(v___x_67_, v_e_61_);
v___x_76_ = lp_mathlib_ZMod_commRing(v___x_75_);
v_toSemiring_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_toSemiring_77_);
lean_dec_ref(v___x_76_);
v___x_78_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_77_);
v_toAdd_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_toAdd_79_);
lean_dec_ref(v___x_78_);
v___x_80_ = lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_cc(v_e_61_);
v_fst_81_ = lean_ctor_get(v___x_80_, 0);
v_snd_82_ = lean_ctor_get(v___x_80_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_101_ == 0)
{
v___x_84_ = v___x_80_;
v_isShared_85_ = v_isSharedCheck_101_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_snd_82_);
lean_inc(v_fst_81_);
lean_dec(v___x_80_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_101_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_100_; 
v_fst_86_ = lean_ctor_get(v_fst_81_, 0);
v_snd_87_ = lean_ctor_get(v_fst_81_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_fst_81_);
if (v_isSharedCheck_100_ == 0)
{
v___x_89_ = v_fst_81_;
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snd_87_);
lean_inc(v_fst_86_);
lean_dec(v_fst_81_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
lean_inc(v_toAdd_74_);
v___x_91_ = lean_apply_2(v_toAdd_74_, v_fst_65_, v_fst_86_);
v___x_92_ = lean_apply_2(v_toAdd_74_, v_snd_66_, v_snd_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_92_);
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_92_);
v___x_94_ = v_reuseFailAlloc_99_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_apply_2(v_toAdd_79_, v_snd_64_, v_snd_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_95_);
lean_ctor_set(v___x_84_, 0, v___x_94_);
v___x_97_ = v___x_84_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
else
{
return v_00_u03b3_62_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_place___boxed(lean_object* v_e_102_, lean_object* v_00_u03b3_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_place(v_e_102_, v_00_u03b3_103_);
lean_dec(v_e_102_);
return v_res_104_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RankGapBounds_ConjInOrbit(uint8_t builtin) {
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
lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg = _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg();
lean_mark_persistent(lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_sg);
lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_c0 = _init_lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_c0();
lean_mark_persistent(lp_tree_Formalism_RankGapBounds_ExistsSmulMemTer_c0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
