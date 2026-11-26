// Lean compiler output
// Module: New.Derivatives.Divisibility.NullFrames
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.Basic public import Lib.General.Algebra.SeriesCongruences
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_PairingSide_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_instDecidableEqPairingSide(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_instDecidableEqPairingSide___boxed(lean_object*, lean_object*);
static const lean_ctor_object lp_GRH_New_PairingSide_instFintype___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GRH_New_PairingSide_instFintype___closed__0 = (const lean_object*)&lp_GRH_New_PairingSide_instFintype___closed__0_value;
static lean_once_cell_t lp_GRH_New_PairingSide_instFintype___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_PairingSide_instFintype___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_instFintype;
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_rootExponent(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_rootExponent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CongruenceChoice_sourceCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CongruenceChoice_partnerCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_CongruenceChoice_imposes(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CongruenceChoice_imposes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_newDirection___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_newDirection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_newDirection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = lp_GRH_New_PairingSide_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_GRH_New_PairingSide_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = lp_GRH_New_PairingSide_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim___redArg(lean_object* v_source_22_){
_start:
{
lean_inc(v_source_22_);
return v_source_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim___redArg___boxed(lean_object* v_source_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_PairingSide_source_elim___redArg(v_source_23_);
lean_dec(v_source_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_source_28_){
_start:
{
lean_inc(v_source_28_);
return v_source_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_source_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_source_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = lp_GRH_New_PairingSide_source_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_source_32_);
lean_dec(v_source_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim___redArg(lean_object* v_partner_35_){
_start:
{
lean_inc(v_partner_35_);
return v_partner_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim___redArg___boxed(lean_object* v_partner_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_GRH_New_PairingSide_partner_elim___redArg(v_partner_36_);
lean_dec(v_partner_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_partner_41_){
_start:
{
lean_inc(v_partner_41_);
return v_partner_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_partner_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_partner_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = lp_GRH_New_PairingSide_partner_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_partner_45_);
lean_dec(v_partner_45_);
return v_res_47_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_PairingSide_ofNat(lean_object* v_n_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_nat_dec_le(v_n_48_, v___x_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_ofNat___boxed(lean_object* v_n_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = lp_GRH_New_PairingSide_ofNat(v_n_53_);
lean_dec(v_n_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_instDecidableEqPairingSide(uint8_t v_x_56_, uint8_t v_y_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lp_GRH_New_PairingSide_ctorIdx(v_x_56_);
v___x_59_ = lp_GRH_New_PairingSide_ctorIdx(v_y_57_);
v___x_60_ = lean_nat_dec_eq(v___x_58_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_instDecidableEqPairingSide___boxed(lean_object* v_x_61_, lean_object* v_y_62_){
_start:
{
uint8_t v_x_20__boxed_63_; uint8_t v_y_21__boxed_64_; uint8_t v_res_65_; lean_object* v_r_66_; 
v_x_20__boxed_63_ = lean_unbox(v_x_61_);
v_y_21__boxed_64_ = lean_unbox(v_y_62_);
v_res_65_ = lp_GRH_New_instDecidableEqPairingSide(v_x_20__boxed_63_, v_y_21__boxed_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_lp_GRH_New_PairingSide_instFintype___closed__1(void){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_71_ = ((lean_object*)(lp_GRH_New_PairingSide_instFintype___closed__0));
v___x_72_ = 0;
v___x_73_ = lean_alloc_closure((void*)(lp_GRH_New_instDecidableEqPairingSide___boxed), 2, 0);
v___x_74_ = lean_box(v___x_72_);
v___x_75_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_73_, v___x_74_, v___x_71_);
return v___x_75_;
}
}
static lean_object* _init_lp_GRH_New_PairingSide_instFintype(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&lp_GRH_New_PairingSide_instFintype___closed__1, &lp_GRH_New_PairingSide_instFintype___closed__1_once, _init_lp_GRH_New_PairingSide_instFintype___closed__1);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place___redArg(uint8_t v_side_77_, lean_object* v_00_u03c3_78_, lean_object* v_00_u03c3_x27_79_){
_start:
{
if (v_side_77_ == 0)
{
lean_inc(v_00_u03c3_78_);
return v_00_u03c3_78_;
}
else
{
lean_inc(v_00_u03c3_x27_79_);
return v_00_u03c3_x27_79_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place___redArg___boxed(lean_object* v_side_80_, lean_object* v_00_u03c3_81_, lean_object* v_00_u03c3_x27_82_){
_start:
{
uint8_t v_side_boxed_83_; lean_object* v_res_84_; 
v_side_boxed_83_ = lean_unbox(v_side_80_);
v_res_84_ = lp_GRH_New_PairingSide_place___redArg(v_side_boxed_83_, v_00_u03c3_81_, v_00_u03c3_x27_82_);
lean_dec(v_00_u03c3_x27_82_);
lean_dec(v_00_u03c3_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place(lean_object* v_00_u03a6_85_, uint8_t v_side_86_, lean_object* v_00_u03c3_87_, lean_object* v_00_u03c3_x27_88_){
_start:
{
if (v_side_86_ == 0)
{
lean_inc(v_00_u03c3_87_);
return v_00_u03c3_87_;
}
else
{
lean_inc(v_00_u03c3_x27_88_);
return v_00_u03c3_x27_88_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_place___boxed(lean_object* v_00_u03a6_89_, lean_object* v_side_90_, lean_object* v_00_u03c3_91_, lean_object* v_00_u03c3_x27_92_){
_start:
{
uint8_t v_side_boxed_93_; lean_object* v_res_94_; 
v_side_boxed_93_ = lean_unbox(v_side_90_);
v_res_94_ = lp_GRH_New_PairingSide_place(v_00_u03a6_89_, v_side_boxed_93_, v_00_u03c3_91_, v_00_u03c3_x27_92_);
lean_dec(v_00_u03c3_x27_92_);
lean_dec(v_00_u03c3_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_rootExponent(uint8_t v_side_95_, lean_object* v_e_96_){
_start:
{
if (v_side_95_ == 0)
{
lean_inc(v_e_96_);
return v_e_96_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = lean_unsigned_to_nat(0u);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_PairingSide_rootExponent___boxed(lean_object* v_side_98_, lean_object* v_e_99_){
_start:
{
uint8_t v_side_boxed_100_; lean_object* v_res_101_; 
v_side_boxed_100_ = lean_unbox(v_side_98_);
v_res_101_ = lp_GRH_New_PairingSide_rootExponent(v_side_boxed_100_, v_e_99_);
lean_dec(v_e_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CongruenceChoice_sourceCount(lean_object* v_c_102_, lean_object* v_h_103_){
_start:
{
lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v_sourceEntries_109_; lean_object* v_sourcePairing_110_; lean_object* v___y_112_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_sourceEntries_109_ = lean_ctor_get(v_c_102_, 0);
lean_inc_ref(v_sourceEntries_109_);
v_sourcePairing_110_ = lean_ctor_get(v_c_102_, 1);
lean_inc_ref(v_sourcePairing_110_);
lean_dec_ref(v_c_102_);
lean_inc(v_h_103_);
v___x_117_ = lean_apply_1(v_sourcePairing_110_, v_h_103_);
v___x_118_ = lean_unbox(v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___y_112_ = v___x_119_;
goto v___jp_111_;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___y_112_ = v___x_120_;
goto v___jp_111_;
}
v___jp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_nat_mul(v_h_103_, v___y_106_);
lean_dec(v_h_103_);
v___x_108_ = lean_nat_add(v___y_105_, v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
v___jp_111_:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
lean_inc(v_h_103_);
v___x_113_ = lean_apply_1(v_sourceEntries_109_, v_h_103_);
v___x_114_ = lean_unbox(v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___y_105_ = v___y_112_;
v___y_106_ = v___x_115_;
goto v___jp_104_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___y_105_ = v___y_112_;
v___y_106_ = v___x_116_;
goto v___jp_104_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CongruenceChoice_partnerCount(lean_object* v_c_121_, lean_object* v_h_122_){
_start:
{
lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v_partnerEntries_128_; lean_object* v_partnerPairing_129_; lean_object* v___y_131_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_partnerEntries_128_ = lean_ctor_get(v_c_121_, 2);
lean_inc_ref(v_partnerEntries_128_);
v_partnerPairing_129_ = lean_ctor_get(v_c_121_, 3);
lean_inc_ref(v_partnerPairing_129_);
lean_dec_ref(v_c_121_);
lean_inc(v_h_122_);
v___x_136_ = lean_apply_1(v_partnerPairing_129_, v_h_122_);
v___x_137_ = lean_unbox(v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___y_131_ = v___x_138_;
goto v___jp_130_;
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___y_131_ = v___x_139_;
goto v___jp_130_;
}
v___jp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_nat_mul(v_h_122_, v___y_125_);
lean_dec(v_h_122_);
v___x_127_ = lean_nat_add(v___y_124_, v___x_126_);
lean_dec(v___x_126_);
return v___x_127_;
}
v___jp_130_:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
lean_inc(v_h_122_);
v___x_132_ = lean_apply_1(v_partnerEntries_128_, v_h_122_);
v___x_133_ = lean_unbox(v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___y_124_ = v___y_131_;
v___y_125_ = v___x_134_;
goto v___jp_123_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v___y_124_ = v___y_131_;
v___y_125_ = v___x_135_;
goto v___jp_123_;
}
}
}
}
LEAN_EXPORT uint8_t lp_GRH_New_CongruenceChoice_imposes(lean_object* v_c_140_, lean_object* v_h_141_, uint8_t v_x_142_, lean_object* v_x_143_){
_start:
{
if (v_x_142_ == 0)
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v_sourcePairing_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_sourcePairing_144_ = lean_ctor_get(v_c_140_, 1);
lean_inc_ref(v_sourcePairing_144_);
lean_dec_ref(v_c_140_);
v___x_145_ = lean_apply_1(v_sourcePairing_144_, v_h_141_);
v___x_146_ = lean_unbox(v___x_145_);
return v___x_146_;
}
else
{
lean_object* v_sourceEntries_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_sourceEntries_147_ = lean_ctor_get(v_c_140_, 0);
lean_inc_ref(v_sourceEntries_147_);
lean_dec_ref(v_c_140_);
v___x_148_ = lean_apply_1(v_sourceEntries_147_, v_h_141_);
v___x_149_ = lean_unbox(v___x_148_);
return v___x_149_;
}
}
else
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v_partnerPairing_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_partnerPairing_150_ = lean_ctor_get(v_c_140_, 3);
lean_inc_ref(v_partnerPairing_150_);
lean_dec_ref(v_c_140_);
v___x_151_ = lean_apply_1(v_partnerPairing_150_, v_h_141_);
v___x_152_ = lean_unbox(v___x_151_);
return v___x_152_;
}
else
{
lean_object* v_partnerEntries_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_partnerEntries_153_ = lean_ctor_get(v_c_140_, 2);
lean_inc_ref(v_partnerEntries_153_);
lean_dec_ref(v_c_140_);
v___x_154_ = lean_apply_1(v_partnerEntries_153_, v_h_141_);
v___x_155_ = lean_unbox(v___x_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CongruenceChoice_imposes___boxed(lean_object* v_c_156_, lean_object* v_h_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_x_43__boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_x_43__boxed_160_ = lean_unbox(v_x_158_);
v_res_161_ = lp_GRH_New_CongruenceChoice_imposes(v_c_156_, v_h_157_, v_x_43__boxed_160_, v_x_159_);
lean_dec(v_x_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus___redArg(lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_pr_165_, lean_object* v_root_166_, lean_object* v_c_167_, lean_object* v_00_u03c4_168_, lean_object* v_h_169_, lean_object* v_x_170_){
_start:
{
lean_object* v_snd_171_; lean_object* v_snd_172_; lean_object* v_fst_173_; lean_object* v_fst_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___y_178_; uint8_t v___x_187_; 
v_snd_171_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_snd_171_);
v_snd_172_ = lean_ctor_get(v_snd_171_, 1);
lean_inc(v_snd_172_);
v_fst_173_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_fst_173_);
lean_dec_ref(v_x_170_);
v_fst_174_ = lean_ctor_get(v_snd_171_, 0);
lean_inc(v_fst_174_);
lean_dec(v_snd_171_);
v_fst_175_ = lean_ctor_get(v_snd_172_, 0);
lean_inc(v_fst_175_);
v_snd_176_ = lean_ctor_get(v_snd_172_, 1);
lean_inc(v_snd_176_);
lean_dec(v_snd_172_);
v___x_187_ = lean_unbox(v_fst_175_);
if (v___x_187_ == 0)
{
lean_dec(v_pr_165_);
lean_inc(v_fst_174_);
v___y_178_ = v_fst_174_;
goto v___jp_177_;
}
else
{
lean_object* v___x_188_; 
lean_inc(v_fst_174_);
lean_inc(v_fst_173_);
v___x_188_ = lean_apply_2(v_pr_165_, v_fst_173_, v_fst_174_);
v___y_178_ = v___x_188_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_apply_2(v_inst_164_, v___y_178_, v_00_u03c4_168_);
v___x_180_ = lean_unbox(v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_snd_176_);
lean_dec(v_fst_175_);
lean_dec(v_fst_174_);
lean_dec(v_fst_173_);
lean_dec(v_h_169_);
lean_dec_ref(v_c_167_);
lean_dec(v_root_166_);
lean_inc(v_inst_163_);
return v_inst_163_;
}
else
{
lean_object* v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; 
lean_inc(v_fst_173_);
v___x_181_ = lean_apply_2(v_c_167_, v_fst_173_, v_fst_174_);
v___x_182_ = lean_unbox(v_fst_175_);
v___x_183_ = lp_GRH_New_CongruenceChoice_imposes(v___x_181_, v_h_169_, v___x_182_, v_snd_176_);
lean_dec(v_snd_176_);
if (v___x_183_ == 0)
{
lean_dec(v_fst_175_);
lean_dec(v_fst_173_);
lean_dec(v_root_166_);
lean_inc(v_inst_163_);
return v_inst_163_;
}
else
{
uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_unbox(v_fst_175_);
lean_dec(v_fst_175_);
v___x_185_ = lp_GRH_New_PairingSide_rootExponent(v___x_184_, v_fst_173_);
lean_dec(v_fst_173_);
v___x_186_ = lean_apply_1(v_root_166_, v___x_185_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus___redArg___boxed(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_pr_191_, lean_object* v_root_192_, lean_object* v_c_193_, lean_object* v_00_u03c4_194_, lean_object* v_h_195_, lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lp_GRH_New_congruenceModulus___redArg(v_inst_189_, v_inst_190_, v_pr_191_, v_root_192_, v_c_193_, v_00_u03c4_194_, v_h_195_, v_x_196_);
lean_dec(v_inst_189_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus(lean_object* v_O_198_, lean_object* v_00_u03a6_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_pr_202_, lean_object* v_S_203_, lean_object* v_root_204_, lean_object* v_c_205_, lean_object* v_00_u03c4_206_, lean_object* v_h_207_, lean_object* v_x_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lp_GRH_New_congruenceModulus___redArg(v_inst_200_, v_inst_201_, v_pr_202_, v_root_204_, v_c_205_, v_00_u03c4_206_, v_h_207_, v_x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_congruenceModulus___boxed(lean_object* v_O_210_, lean_object* v_00_u03a6_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_pr_214_, lean_object* v_S_215_, lean_object* v_root_216_, lean_object* v_c_217_, lean_object* v_00_u03c4_218_, lean_object* v_h_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_GRH_New_congruenceModulus(v_O_210_, v_00_u03a6_211_, v_inst_212_, v_inst_213_, v_pr_214_, v_S_215_, v_root_216_, v_c_217_, v_00_u03c4_218_, v_h_219_, v_x_220_);
lean_dec(v_S_215_);
lean_dec(v_inst_212_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter___redArg(lean_object* v_x_222_, lean_object* v_h__1_223_){
_start:
{
lean_object* v_snd_224_; lean_object* v_snd_225_; lean_object* v_fst_226_; lean_object* v_fst_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; 
v_snd_224_ = lean_ctor_get(v_x_222_, 1);
lean_inc(v_snd_224_);
v_snd_225_ = lean_ctor_get(v_snd_224_, 1);
lean_inc(v_snd_225_);
v_fst_226_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_fst_226_);
lean_dec_ref(v_x_222_);
v_fst_227_ = lean_ctor_get(v_snd_224_, 0);
lean_inc(v_fst_227_);
lean_dec(v_snd_224_);
v_fst_228_ = lean_ctor_get(v_snd_225_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_snd_225_, 1);
lean_inc(v_snd_229_);
lean_dec(v_snd_225_);
v___x_230_ = lean_apply_4(v_h__1_223_, v_fst_226_, v_fst_227_, v_fst_228_, v_snd_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter(lean_object* v_00_u03a6_231_, lean_object* v_S_232_, lean_object* v_h_233_, lean_object* v_motive_234_, lean_object* v_x_235_, lean_object* v_h__1_236_){
_start:
{
lean_object* v_snd_237_; lean_object* v_snd_238_; lean_object* v_fst_239_; lean_object* v_fst_240_; lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_243_; 
v_snd_237_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_snd_237_);
v_snd_238_ = lean_ctor_get(v_snd_237_, 1);
lean_inc(v_snd_238_);
v_fst_239_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_fst_239_);
lean_dec_ref(v_x_235_);
v_fst_240_ = lean_ctor_get(v_snd_237_, 0);
lean_inc(v_fst_240_);
lean_dec(v_snd_237_);
v_fst_241_ = lean_ctor_get(v_snd_238_, 0);
lean_inc(v_fst_241_);
v_snd_242_ = lean_ctor_get(v_snd_238_, 1);
lean_inc(v_snd_242_);
lean_dec(v_snd_238_);
v___x_243_ = lean_apply_4(v_h__1_236_, v_fst_239_, v_fst_240_, v_fst_241_, v_snd_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter___boxed(lean_object* v_00_u03a6_244_, lean_object* v_S_245_, lean_object* v_h_246_, lean_object* v_motive_247_, lean_object* v_x_248_, lean_object* v_h__1_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_congruenceModulus_match__1_splitter(v_00_u03a6_244_, v_S_245_, v_h_246_, v_motive_247_, v_x_248_, v_h__1_249_);
lean_dec(v_h_246_);
lean_dec(v_S_245_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_newDirection___redArg___lam__0(lean_object* v_y_251_, lean_object* v_00_u03c4_252_, lean_object* v_a_253_, lean_object* v_k_x27_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_apply_3(v_y_251_, v_00_u03c4_252_, v_a_253_, v_k_x27_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_newDirection___redArg(lean_object* v_inst_256_, lean_object* v_g_257_, lean_object* v_y_258_, lean_object* v_00_u03c4_259_, lean_object* v_h_260_, lean_object* v_k_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_toSemiring_263_; lean_object* v___x_264_; lean_object* v_toMul_265_; lean_object* v_toAddCommMonoid_266_; lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_toSemiring_263_ = lean_ctor_get(v_inst_256_, 0);
lean_inc_ref_n(v_toSemiring_263_, 2);
lean_dec_ref(v_inst_256_);
v___x_264_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_263_);
v_toMul_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_toMul_265_);
lean_dec_ref(v___x_264_);
v_toAddCommMonoid_266_ = lean_ctor_get(v_toSemiring_263_, 0);
lean_inc_ref(v_toAddCommMonoid_266_);
lean_dec_ref(v_toSemiring_263_);
lean_inc(v_00_u03c4_259_);
v___f_267_ = lean_alloc_closure((void*)(lp_GRH_New_newDirection___redArg___lam__0), 4, 3);
lean_closure_set(v___f_267_, 0, v_y_258_);
lean_closure_set(v___f_267_, 1, v_00_u03c4_259_);
lean_closure_set(v___f_267_, 2, v_a_262_);
lean_inc(v_h_260_);
v___x_268_ = l_List_finRange(v_h_260_);
v___x_269_ = lean_apply_3(v_g_257_, v_00_u03c4_259_, v_h_260_, v_k_261_);
v___x_270_ = lp_mathlib_dotProduct___redArg(v___x_268_, v_toMul_265_, v_toAddCommMonoid_266_, v___x_269_, v___f_267_);
lean_dec_ref(v_toAddCommMonoid_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_newDirection(lean_object* v_00_u03a6_271_, lean_object* v_n_272_, lean_object* v_R_273_, lean_object* v_inst_274_, lean_object* v_g_275_, lean_object* v_y_276_, lean_object* v_00_u03c4_277_, lean_object* v_h_278_, lean_object* v_k_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lp_GRH_New_newDirection___redArg(v_inst_274_, v_g_275_, v_y_276_, v_00_u03c4_277_, v_h_278_, v_k_279_, v_a_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___redArg(uint8_t v_side_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
if (v_side_282_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_h__2_284_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_apply_1(v_h__1_283_, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_h__1_283_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_apply_1(v_h__2_284_, v___x_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___redArg___boxed(lean_object* v_side_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_){
_start:
{
uint8_t v_side_24__boxed_292_; lean_object* v_res_293_; 
v_side_24__boxed_292_ = lean_unbox(v_side_289_);
v_res_293_ = lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___redArg(v_side_24__boxed_292_, v_h__1_290_, v_h__2_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter(lean_object* v_motive_294_, uint8_t v_side_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
if (v_side_295_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_h__2_297_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v_h__1_296_, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_h__1_296_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__2_297_, v___x_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter___boxed(lean_object* v_motive_302_, lean_object* v_side_303_, lean_object* v_h__1_304_, lean_object* v_h__2_305_){
_start:
{
uint8_t v_side_35__boxed_306_; lean_object* v_res_307_; 
v_side_35__boxed_306_ = lean_unbox(v_side_303_);
v_res_307_ = lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_PairingSide_place_match__1_splitter(v_motive_302_, v_side_35__boxed_306_, v_h__1_304_, v_h__2_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter___redArg(lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_){
_start:
{
lean_object* v_snd_312_; lean_object* v_snd_313_; lean_object* v_fst_314_; uint8_t v___x_315_; 
v_snd_312_ = lean_ctor_get(v_x_308_, 1);
lean_inc(v_snd_312_);
v_snd_313_ = lean_ctor_get(v_snd_312_, 1);
v_fst_314_ = lean_ctor_get(v_snd_313_, 0);
v___x_315_ = lean_unbox(v_fst_314_);
if (v___x_315_ == 0)
{
lean_object* v_snd_316_; 
lean_dec(v_h__2_310_);
v_snd_316_ = lean_ctor_get(v_snd_313_, 1);
if (lean_obj_tag(v_snd_316_) == 0)
{
lean_object* v_fst_317_; lean_object* v_fst_318_; lean_object* v___x_319_; 
lean_dec(v_h__3_311_);
v_fst_317_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_fst_317_);
lean_dec_ref(v_x_308_);
v_fst_318_ = lean_ctor_get(v_snd_312_, 0);
lean_inc(v_fst_318_);
lean_dec(v_snd_312_);
v___x_319_ = lean_apply_2(v_h__1_309_, v_fst_317_, v_fst_318_);
return v___x_319_;
}
else
{
lean_object* v_fst_320_; lean_object* v_fst_321_; lean_object* v_val_322_; lean_object* v___x_323_; 
lean_inc_ref(v_snd_316_);
lean_inc(v_fst_314_);
lean_dec(v_h__1_309_);
v_fst_320_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_fst_320_);
lean_dec_ref(v_x_308_);
v_fst_321_ = lean_ctor_get(v_snd_312_, 0);
lean_inc(v_fst_321_);
lean_dec(v_snd_312_);
v_val_322_ = lean_ctor_get(v_snd_316_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_snd_316_, 1);
v___x_323_ = lean_apply_4(v_h__3_311_, v_fst_320_, v_fst_321_, v_fst_314_, v_val_322_);
return v___x_323_;
}
}
else
{
lean_object* v_snd_324_; 
lean_dec(v_h__1_309_);
v_snd_324_ = lean_ctor_get(v_snd_313_, 1);
if (lean_obj_tag(v_snd_324_) == 0)
{
lean_object* v_fst_325_; lean_object* v_fst_326_; lean_object* v___x_327_; 
lean_dec(v_h__3_311_);
v_fst_325_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_fst_325_);
lean_dec_ref(v_x_308_);
v_fst_326_ = lean_ctor_get(v_snd_312_, 0);
lean_inc(v_fst_326_);
lean_dec(v_snd_312_);
v___x_327_ = lean_apply_2(v_h__2_310_, v_fst_325_, v_fst_326_);
return v___x_327_;
}
else
{
lean_object* v_fst_328_; lean_object* v_fst_329_; lean_object* v_val_330_; lean_object* v___x_331_; 
lean_inc_ref(v_snd_324_);
lean_inc(v_fst_314_);
lean_dec(v_h__2_310_);
v_fst_328_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_fst_328_);
lean_dec_ref(v_x_308_);
v_fst_329_ = lean_ctor_get(v_snd_312_, 0);
lean_inc(v_fst_329_);
lean_dec(v_snd_312_);
v_val_330_ = lean_ctor_get(v_snd_324_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v_snd_324_, 1);
v___x_331_ = lean_apply_4(v_h__3_311_, v_fst_328_, v_fst_329_, v_fst_314_, v_val_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter(lean_object* v_00_u03a6_332_, lean_object* v_S_333_, lean_object* v_h_334_, lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_h__1_337_, lean_object* v_h__2_338_, lean_object* v_h__3_339_){
_start:
{
lean_object* v_snd_340_; lean_object* v_snd_341_; lean_object* v_fst_342_; uint8_t v___x_343_; 
v_snd_340_ = lean_ctor_get(v_x_336_, 1);
lean_inc(v_snd_340_);
v_snd_341_ = lean_ctor_get(v_snd_340_, 1);
v_fst_342_ = lean_ctor_get(v_snd_341_, 0);
v___x_343_ = lean_unbox(v_fst_342_);
if (v___x_343_ == 0)
{
lean_object* v_snd_344_; 
lean_dec(v_h__2_338_);
v_snd_344_ = lean_ctor_get(v_snd_341_, 1);
if (lean_obj_tag(v_snd_344_) == 0)
{
lean_object* v_fst_345_; lean_object* v_fst_346_; lean_object* v___x_347_; 
lean_dec(v_h__3_339_);
v_fst_345_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_fst_345_);
lean_dec_ref(v_x_336_);
v_fst_346_ = lean_ctor_get(v_snd_340_, 0);
lean_inc(v_fst_346_);
lean_dec(v_snd_340_);
v___x_347_ = lean_apply_2(v_h__1_337_, v_fst_345_, v_fst_346_);
return v___x_347_;
}
else
{
lean_object* v_fst_348_; lean_object* v_fst_349_; lean_object* v_val_350_; lean_object* v___x_351_; 
lean_inc_ref(v_snd_344_);
lean_inc(v_fst_342_);
lean_dec(v_h__1_337_);
v_fst_348_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_fst_348_);
lean_dec_ref(v_x_336_);
v_fst_349_ = lean_ctor_get(v_snd_340_, 0);
lean_inc(v_fst_349_);
lean_dec(v_snd_340_);
v_val_350_ = lean_ctor_get(v_snd_344_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v_snd_344_, 1);
v___x_351_ = lean_apply_4(v_h__3_339_, v_fst_348_, v_fst_349_, v_fst_342_, v_val_350_);
return v___x_351_;
}
}
else
{
lean_object* v_snd_352_; 
lean_dec(v_h__1_337_);
v_snd_352_ = lean_ctor_get(v_snd_341_, 1);
if (lean_obj_tag(v_snd_352_) == 0)
{
lean_object* v_fst_353_; lean_object* v_fst_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_339_);
v_fst_353_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_fst_353_);
lean_dec_ref(v_x_336_);
v_fst_354_ = lean_ctor_get(v_snd_340_, 0);
lean_inc(v_fst_354_);
lean_dec(v_snd_340_);
v___x_355_ = lean_apply_2(v_h__2_338_, v_fst_353_, v_fst_354_);
return v___x_355_;
}
else
{
lean_object* v_fst_356_; lean_object* v_fst_357_; lean_object* v_val_358_; lean_object* v___x_359_; 
lean_inc_ref(v_snd_352_);
lean_inc(v_fst_342_);
lean_dec(v_h__2_338_);
v_fst_356_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_fst_356_);
lean_dec_ref(v_x_336_);
v_fst_357_ = lean_ctor_get(v_snd_340_, 0);
lean_inc(v_fst_357_);
lean_dec(v_snd_340_);
v_val_358_ = lean_ctor_get(v_snd_352_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v_snd_352_, 1);
v___x_359_ = lean_apply_4(v_h__3_339_, v_fst_356_, v_fst_357_, v_fst_342_, v_val_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter___boxed(lean_object* v_00_u03a6_360_, lean_object* v_S_361_, lean_object* v_h_362_, lean_object* v_motive_363_, lean_object* v_x_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_, lean_object* v_h__3_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = lp_GRH___private_New_Derivatives_Divisibility_NullFrames_0__New_exists__newDirection__dvd_match__1__1_splitter(v_00_u03a6_360_, v_S_361_, v_h_362_, v_motive_363_, v_x_364_, v_h__1_365_, v_h__2_366_, v_h__3_367_);
lean_dec(v_h_362_);
lean_dec(v_S_361_);
return v_res_368_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_SeriesCongruences(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_Divisibility_NullFrames(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_SeriesCongruences(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_PairingSide_instFintype = _init_lp_GRH_New_PairingSide_instFintype();
lean_mark_persistent(lp_GRH_New_PairingSide_instFintype);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
