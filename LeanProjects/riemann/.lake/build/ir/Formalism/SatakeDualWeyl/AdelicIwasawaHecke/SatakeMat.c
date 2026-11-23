// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeMat
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementE public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Equiv_toPEquiv___redArg(lean_object*);
lean_object* lp_mathlib_PEquiv_toMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_add___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_sub___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeU___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeP___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_S_3_, lean_object* v_c_4_, lean_object* v_a_5_, lean_object* v_l_6_){
_start:
{
uint8_t v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_13_ = lean_nat_dec_lt(v_a_5_, v_l_6_);
v___x_14_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_14_, 0, v_n_2_);
lean_inc(v_S_3_);
lean_inc(v_a_5_);
lean_inc_ref(v___x_14_);
v___x_15_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_14_, v_a_5_, v_S_3_);
if (v___x_15_ == 0)
{
lean_dec_ref(v___x_14_);
lean_dec(v_l_6_);
lean_dec(v_a_5_);
lean_dec(v_c_4_);
lean_dec(v_S_3_);
goto v___jp_7_;
}
else
{
uint8_t v___x_16_; 
lean_inc(v_l_6_);
v___x_16_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_14_, v_l_6_, v_S_3_);
if (v___x_16_ == 0)
{
if (v___x_15_ == 0)
{
lean_dec(v_l_6_);
lean_dec(v_a_5_);
lean_dec(v_c_4_);
goto v___jp_7_;
}
else
{
if (v___x_13_ == 0)
{
lean_dec(v_l_6_);
lean_dec(v_a_5_);
lean_dec(v_c_4_);
goto v___jp_7_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v_a_5_);
lean_ctor_set(v___x_17_, 1, v_l_6_);
v___x_18_ = lean_apply_1(v_c_4_, v___x_17_);
return v___x_18_;
}
}
}
else
{
lean_dec(v_l_6_);
lean_dec(v_a_5_);
lean_dec(v_c_4_);
goto v___jp_7_;
}
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toSemiring_10_; lean_object* v___x_11_; lean_object* v_toZero_12_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_9_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_8_);
v_toSemiring_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toSemiring_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_10_);
v_toZero_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_toZero_12_);
lean_dec_ref(v___x_11_);
return v_toZero_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN___redArg___boxed(lean_object* v_inst_19_, lean_object* v_n_20_, lean_object* v_S_21_, lean_object* v_c_22_, lean_object* v_a_23_, lean_object* v_l_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_UG_P_satakeN___redArg(v_inst_19_, v_n_20_, v_S_21_, v_c_22_, v_a_23_, v_l_24_);
lean_dec_ref(v_inst_19_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN(lean_object* v_L_26_, lean_object* v_inst_27_, lean_object* v_O_28_, lean_object* v_n_29_, lean_object* v_S_30_, lean_object* v_c_31_, lean_object* v_a_32_, lean_object* v_l_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_UG_P_satakeN___redArg(v_inst_27_, v_n_29_, v_S_30_, v_c_31_, v_a_32_, v_l_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeN___boxed(lean_object* v_L_35_, lean_object* v_inst_36_, lean_object* v_O_37_, lean_object* v_n_38_, lean_object* v_S_39_, lean_object* v_c_40_, lean_object* v_a_41_, lean_object* v_l_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_UG_P_satakeN(v_L_35_, v_inst_36_, v_O_37_, v_n_38_, v_S_39_, v_c_40_, v_a_41_, v_l_42_);
lean_dec_ref(v_inst_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD___redArg___lam__0(lean_object* v___x_44_, lean_object* v_S_45_, lean_object* v_inst_46_, lean_object* v_00_u03c0_47_, lean_object* v_a_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_44_, v_a_48_, v_S_45_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v_toRing_51_; lean_object* v___x_52_; lean_object* v_toAddMonoidWithOne_53_; lean_object* v_toOne_54_; 
v___x_50_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_46_);
v_toRing_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc_ref(v_toRing_51_);
lean_dec_ref(v___x_50_);
v___x_52_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_51_);
v_toAddMonoidWithOne_53_ = lean_ctor_get(v___x_52_, 1);
lean_inc_ref(v_toAddMonoidWithOne_53_);
lean_dec_ref(v___x_52_);
v_toOne_54_ = lean_ctor_get(v_toAddMonoidWithOne_53_, 2);
lean_inc(v_toOne_54_);
lean_dec_ref(v_toAddMonoidWithOne_53_);
return v_toOne_54_;
}
else
{
lean_dec_ref(v_inst_46_);
lean_inc(v_00_u03c0_47_);
return v_00_u03c0_47_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD___redArg___lam__0___boxed(lean_object* v___x_55_, lean_object* v_S_56_, lean_object* v_inst_57_, lean_object* v_00_u03c0_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_UG_P_satakeD___redArg___lam__0(v___x_55_, v_S_56_, v_inst_57_, v_00_u03c0_58_, v_a_59_);
lean_dec(v_00_u03c0_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD___redArg(lean_object* v_inst_61_, lean_object* v_n_62_, lean_object* v_00_u03c0_63_, lean_object* v_S_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toSemiring_69_; lean_object* v___x_70_; lean_object* v_toZero_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___x_74_; 
v___x_67_ = lp_mathlib_Field_toSemifield___redArg(v_inst_61_);
v___x_68_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_67_);
v_toSemiring_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_toSemiring_69_);
lean_dec_ref(v___x_68_);
v___x_70_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_69_);
v_toZero_71_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_toZero_71_);
lean_dec_ref(v___x_70_);
v___x_72_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_72_, 0, v_n_62_);
lean_inc_ref(v___x_72_);
v___f_73_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeD___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_73_, 0, v___x_72_);
lean_closure_set(v___f_73_, 1, v_S_64_);
lean_closure_set(v___f_73_, 2, v_inst_61_);
lean_closure_set(v___f_73_, 3, v_00_u03c0_63_);
v___x_74_ = lp_mathlib_Matrix_diagonal___redArg(v___x_72_, v_toZero_71_, v___f_73_, v_a_65_, v_a_66_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeD(lean_object* v_L_75_, lean_object* v_inst_76_, lean_object* v_n_77_, lean_object* v_00_u03c0_78_, lean_object* v_S_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lp_tree_Formalism_UG_P_satakeD___redArg(v_inst_76_, v_n_77_, v_00_u03c0_78_, v_S_79_, v_a_80_, v_a_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0(lean_object* v_toOne_83_, lean_object* v_x_84_){
_start:
{
lean_inc(v_toOne_83_);
return v_toOne_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0___boxed(lean_object* v_toOne_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0(v_toOne_85_, v_x_86_);
lean_dec(v_x_86_);
lean_dec(v_toOne_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__1(lean_object* v_inst_88_, lean_object* v_n_89_, lean_object* v_00_u03c0_90_, lean_object* v_S_91_, lean_object* v___y_92_, lean_object* v_j_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_tree_Formalism_UG_P_satakeD___redArg(v_inst_88_, v_n_89_, v_00_u03c0_90_, v_S_91_, v_j_93_, v___y_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__2(lean_object* v___x_95_, lean_object* v_toZero_96_, lean_object* v___f_97_, lean_object* v___y_98_, lean_object* v_inst_99_, lean_object* v_n_100_, lean_object* v_S_101_, lean_object* v_c_102_, lean_object* v_toAdd_103_, lean_object* v_j_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc(v_j_104_);
lean_inc(v___y_98_);
v___x_105_ = lp_mathlib_Matrix_diagonal___redArg(v___x_95_, v_toZero_96_, v___f_97_, v___y_98_, v_j_104_);
v___x_106_ = lp_tree_Formalism_UG_P_satakeN___redArg(v_inst_99_, v_n_100_, v_S_101_, v_c_102_, v___y_98_, v_j_104_);
v___x_107_ = lean_apply_2(v_toAdd_103_, v___x_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__2___boxed(lean_object* v___x_108_, lean_object* v_toZero_109_, lean_object* v___f_110_, lean_object* v___y_111_, lean_object* v_inst_112_, lean_object* v_n_113_, lean_object* v_S_114_, lean_object* v_c_115_, lean_object* v_toAdd_116_, lean_object* v_j_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_tree_Formalism_UG_P_satakeGL___redArg___lam__2(v___x_108_, v_toZero_109_, v___f_110_, v___y_111_, v_inst_112_, v_n_113_, v_S_114_, v_c_115_, v_toAdd_116_, v_j_117_);
lean_dec_ref(v_inst_112_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__3(lean_object* v_inst_119_, lean_object* v_n_120_, lean_object* v_00_u03c0_121_, lean_object* v_S_122_, lean_object* v___x_123_, lean_object* v_toZero_124_, lean_object* v___f_125_, lean_object* v_c_126_, lean_object* v_toAdd_127_, lean_object* v___x_128_, lean_object* v_toMul_129_, lean_object* v_toAddCommMonoid_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
lean_inc(v_S_122_);
lean_inc(v_n_120_);
lean_inc_ref(v_inst_119_);
v___f_133_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__1), 6, 5);
lean_closure_set(v___f_133_, 0, v_inst_119_);
lean_closure_set(v___f_133_, 1, v_n_120_);
lean_closure_set(v___f_133_, 2, v_00_u03c0_121_);
lean_closure_set(v___f_133_, 3, v_S_122_);
lean_closure_set(v___f_133_, 4, v___y_132_);
v___f_134_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_134_, 0, v___x_123_);
lean_closure_set(v___f_134_, 1, v_toZero_124_);
lean_closure_set(v___f_134_, 2, v___f_125_);
lean_closure_set(v___f_134_, 3, v___y_131_);
lean_closure_set(v___f_134_, 4, v_inst_119_);
lean_closure_set(v___f_134_, 5, v_n_120_);
lean_closure_set(v___f_134_, 6, v_S_122_);
lean_closure_set(v___f_134_, 7, v_c_126_);
lean_closure_set(v___f_134_, 8, v_toAdd_127_);
v___x_135_ = lp_mathlib_dotProduct___redArg(v___x_128_, v_toMul_129_, v_toAddCommMonoid_130_, v___f_134_, v___f_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__3___boxed(lean_object* v_inst_136_, lean_object* v_n_137_, lean_object* v_00_u03c0_138_, lean_object* v_S_139_, lean_object* v___x_140_, lean_object* v_toZero_141_, lean_object* v___f_142_, lean_object* v_c_143_, lean_object* v_toAdd_144_, lean_object* v___x_145_, lean_object* v_toMul_146_, lean_object* v_toAddCommMonoid_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = lp_tree_Formalism_UG_P_satakeGL___redArg___lam__3(v_inst_136_, v_n_137_, v_00_u03c0_138_, v_S_139_, v___x_140_, v_toZero_141_, v___f_142_, v_c_143_, v_toAdd_144_, v___x_145_, v_toMul_146_, v_toAddCommMonoid_147_, v___y_148_, v___y_149_);
lean_dec_ref(v_toAddCommMonoid_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__4(lean_object* v___x_151_, lean_object* v_toZero_152_, lean_object* v___f_153_, lean_object* v___y_154_, lean_object* v_inst_155_, lean_object* v_n_156_, lean_object* v_S_157_, lean_object* v_c_158_, lean_object* v_toSub_159_, lean_object* v_j_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
lean_inc(v___y_154_);
lean_inc(v_j_160_);
v___x_161_ = lp_mathlib_Matrix_diagonal___redArg(v___x_151_, v_toZero_152_, v___f_153_, v_j_160_, v___y_154_);
v___x_162_ = lp_tree_Formalism_UG_P_satakeN___redArg(v_inst_155_, v_n_156_, v_S_157_, v_c_158_, v_j_160_, v___y_154_);
v___x_163_ = lean_apply_2(v_toSub_159_, v___x_161_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__4___boxed(lean_object* v___x_164_, lean_object* v_toZero_165_, lean_object* v___f_166_, lean_object* v___y_167_, lean_object* v_inst_168_, lean_object* v_n_169_, lean_object* v_S_170_, lean_object* v_c_171_, lean_object* v_toSub_172_, lean_object* v_j_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_tree_Formalism_UG_P_satakeGL___redArg___lam__4(v___x_164_, v_toZero_165_, v___f_166_, v___y_167_, v_inst_168_, v_n_169_, v_S_170_, v_c_171_, v_toSub_172_, v_j_173_);
lean_dec_ref(v_inst_168_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__5(lean_object* v_inst_175_, lean_object* v_n_176_, lean_object* v___x_177_, lean_object* v_S_178_, lean_object* v___y_179_, lean_object* v_j_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lp_tree_Formalism_UG_P_satakeD___redArg(v_inst_175_, v_n_176_, v___x_177_, v_S_178_, v___y_179_, v_j_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__6(lean_object* v___x_182_, lean_object* v_toZero_183_, lean_object* v___f_184_, lean_object* v_inst_185_, lean_object* v_n_186_, lean_object* v_S_187_, lean_object* v_c_188_, lean_object* v_toSub_189_, lean_object* v___x_190_, lean_object* v___x_191_, lean_object* v_toMul_192_, lean_object* v_toAddCommMonoid_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
lean_inc(v_S_187_);
lean_inc(v_n_186_);
lean_inc_ref(v_inst_185_);
v___f_196_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_196_, 0, v___x_182_);
lean_closure_set(v___f_196_, 1, v_toZero_183_);
lean_closure_set(v___f_196_, 2, v___f_184_);
lean_closure_set(v___f_196_, 3, v___y_195_);
lean_closure_set(v___f_196_, 4, v_inst_185_);
lean_closure_set(v___f_196_, 5, v_n_186_);
lean_closure_set(v___f_196_, 6, v_S_187_);
lean_closure_set(v___f_196_, 7, v_c_188_);
lean_closure_set(v___f_196_, 8, v_toSub_189_);
v___f_197_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__5), 6, 5);
lean_closure_set(v___f_197_, 0, v_inst_185_);
lean_closure_set(v___f_197_, 1, v_n_186_);
lean_closure_set(v___f_197_, 2, v___x_190_);
lean_closure_set(v___f_197_, 3, v_S_187_);
lean_closure_set(v___f_197_, 4, v___y_194_);
v___x_198_ = lp_mathlib_dotProduct___redArg(v___x_191_, v_toMul_192_, v_toAddCommMonoid_193_, v___f_197_, v___f_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg___lam__6___boxed(lean_object* v___x_199_, lean_object* v_toZero_200_, lean_object* v___f_201_, lean_object* v_inst_202_, lean_object* v_n_203_, lean_object* v_S_204_, lean_object* v_c_205_, lean_object* v_toSub_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_toMul_209_, lean_object* v_toAddCommMonoid_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = lp_tree_Formalism_UG_P_satakeGL___redArg___lam__6(v___x_199_, v_toZero_200_, v___f_201_, v_inst_202_, v_n_203_, v_S_204_, v_c_205_, v_toSub_206_, v___x_207_, v___x_208_, v_toMul_209_, v_toAddCommMonoid_210_, v___y_211_, v___y_212_);
lean_dec_ref(v_toAddCommMonoid_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL___redArg(lean_object* v_inst_214_, lean_object* v_n_215_, lean_object* v_00_u03c0_216_, lean_object* v_S_217_, lean_object* v_c_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_toSemiring_221_; lean_object* v___x_222_; lean_object* v_toMul_223_; lean_object* v_toAdd_224_; lean_object* v_toAddCommMonoid_225_; lean_object* v___x_226_; lean_object* v_toZero_227_; lean_object* v___x_228_; lean_object* v_toRing_229_; lean_object* v___x_230_; lean_object* v_toAddMonoidWithOne_231_; lean_object* v_toOne_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toInv_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_251_; 
v___x_219_ = lp_mathlib_Field_toSemifield___redArg(v_inst_214_);
lean_inc_ref(v___x_219_);
v___x_220_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_219_);
v_toSemiring_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_ref_n(v_toSemiring_221_, 2);
lean_dec_ref(v___x_220_);
v___x_222_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_221_);
v_toMul_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_toMul_223_);
v_toAdd_224_ = lean_ctor_get(v___x_222_, 1);
lean_inc(v_toAdd_224_);
lean_dec_ref(v___x_222_);
v_toAddCommMonoid_225_ = lean_ctor_get(v_toSemiring_221_, 0);
lean_inc_ref(v_toAddCommMonoid_225_);
v___x_226_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_221_);
v_toZero_227_ = lean_ctor_get(v___x_226_, 1);
lean_inc(v_toZero_227_);
lean_dec_ref(v___x_226_);
lean_inc_ref(v_inst_214_);
v___x_228_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_214_);
v_toRing_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_toRing_229_);
lean_dec_ref(v___x_228_);
v___x_230_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_229_);
v_toAddMonoidWithOne_231_ = lean_ctor_get(v___x_230_, 1);
lean_inc_ref(v_toAddMonoidWithOne_231_);
v_toOne_232_ = lean_ctor_get(v_toAddMonoidWithOne_231_, 2);
lean_inc(v_toOne_232_);
lean_dec_ref(v_toAddMonoidWithOne_231_);
v___x_233_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_219_);
lean_dec_ref(v___x_219_);
v___x_234_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_233_);
v___x_235_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_234_);
lean_dec_ref(v___x_234_);
v_toInv_236_ = lean_ctor_get(v___x_235_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v___x_235_, 0);
lean_dec(v_unused_252_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_251_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toInv_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_251_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v_toSub_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___f_244_; lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_249_; 
v___x_240_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_230_);
lean_dec_ref(v___x_230_);
v_toSub_241_ = lean_ctor_get(v___x_240_, 2);
lean_inc(v_toSub_241_);
lean_dec_ref(v___x_240_);
lean_inc_n(v_n_215_, 3);
v___x_242_ = l_List_finRange(v_n_215_);
v___x_243_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_243_, 0, v_n_215_);
v___f_244_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_244_, 0, v_toOne_232_);
lean_inc_ref(v_toAddCommMonoid_225_);
lean_inc(v_toMul_223_);
lean_inc(v___x_242_);
lean_inc(v_c_218_);
lean_inc_ref(v___f_244_);
lean_inc(v_toZero_227_);
lean_inc_ref(v___x_243_);
lean_inc(v_S_217_);
lean_inc(v_00_u03c0_216_);
lean_inc_ref(v_inst_214_);
v___f_245_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_245_, 0, v_inst_214_);
lean_closure_set(v___f_245_, 1, v_n_215_);
lean_closure_set(v___f_245_, 2, v_00_u03c0_216_);
lean_closure_set(v___f_245_, 3, v_S_217_);
lean_closure_set(v___f_245_, 4, v___x_243_);
lean_closure_set(v___f_245_, 5, v_toZero_227_);
lean_closure_set(v___f_245_, 6, v___f_244_);
lean_closure_set(v___f_245_, 7, v_c_218_);
lean_closure_set(v___f_245_, 8, v_toAdd_224_);
lean_closure_set(v___f_245_, 9, v___x_242_);
lean_closure_set(v___f_245_, 10, v_toMul_223_);
lean_closure_set(v___f_245_, 11, v_toAddCommMonoid_225_);
v___x_246_ = lean_apply_1(v_toInv_236_, v_00_u03c0_216_);
v___f_247_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__6___boxed), 14, 12);
lean_closure_set(v___f_247_, 0, v___x_243_);
lean_closure_set(v___f_247_, 1, v_toZero_227_);
lean_closure_set(v___f_247_, 2, v___f_244_);
lean_closure_set(v___f_247_, 3, v_inst_214_);
lean_closure_set(v___f_247_, 4, v_n_215_);
lean_closure_set(v___f_247_, 5, v_S_217_);
lean_closure_set(v___f_247_, 6, v_c_218_);
lean_closure_set(v___f_247_, 7, v_toSub_241_);
lean_closure_set(v___f_247_, 8, v___x_246_);
lean_closure_set(v___f_247_, 9, v___x_242_);
lean_closure_set(v___f_247_, 10, v_toMul_223_);
lean_closure_set(v___f_247_, 11, v_toAddCommMonoid_225_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___f_247_);
lean_ctor_set(v___x_238_, 0, v___f_245_);
v___x_249_ = v___x_238_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___f_245_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___f_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeGL(lean_object* v_L_253_, lean_object* v_inst_254_, lean_object* v_O_255_, lean_object* v_n_256_, lean_object* v_00_u03c0_257_, lean_object* v_h_u03c0_258_, lean_object* v_S_259_, lean_object* v_c_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lp_tree_Formalism_UG_P_satakeGL___redArg(v_inst_254_, v_n_256_, v_00_u03c0_257_, v_S_259_, v_c_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeU___redArg(lean_object* v_inst_262_, lean_object* v_O_263_, lean_object* v_n_264_, lean_object* v_S_265_, lean_object* v_c_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_toSemiring_269_; lean_object* v___x_270_; lean_object* v_toAdd_271_; lean_object* v___x_272_; lean_object* v_toZero_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_293_; 
v___x_267_ = lp_mathlib_Field_toSemifield___redArg(v_inst_262_);
v___x_268_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_267_);
v_toSemiring_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref_n(v_toSemiring_269_, 2);
lean_dec_ref(v___x_268_);
v___x_270_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_269_);
v_toAdd_271_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_toAdd_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_269_);
v_toZero_273_ = lean_ctor_get(v___x_272_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v___x_272_, 0);
lean_dec(v_unused_294_);
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_toZero_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v_toRing_278_; lean_object* v___x_279_; lean_object* v_toAddMonoidWithOne_280_; lean_object* v_toOne_281_; lean_object* v___x_282_; lean_object* v_toSub_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
lean_inc_ref(v_inst_262_);
v___x_277_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_262_);
v_toRing_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_ref(v_toRing_278_);
lean_dec_ref(v___x_277_);
v___x_279_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_278_);
v_toAddMonoidWithOne_280_ = lean_ctor_get(v___x_279_, 1);
lean_inc_ref(v_toAddMonoidWithOne_280_);
v_toOne_281_ = lean_ctor_get(v_toAddMonoidWithOne_280_, 2);
lean_inc(v_toOne_281_);
lean_dec_ref(v_toAddMonoidWithOne_280_);
v___x_282_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_279_);
lean_dec_ref(v___x_279_);
v_toSub_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc(v_toSub_283_);
lean_dec_ref(v___x_282_);
lean_inc(v_n_264_);
v___x_284_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_284_, 0, v_n_264_);
v___f_285_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeGL___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_285_, 0, v_toOne_281_);
v___x_286_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_286_, 0, lean_box(0));
lean_closure_set(v___x_286_, 1, lean_box(0));
lean_closure_set(v___x_286_, 2, v___x_284_);
lean_closure_set(v___x_286_, 3, v_toZero_273_);
lean_closure_set(v___x_286_, 4, v___f_285_);
v___x_287_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeN___boxed), 8, 6);
lean_closure_set(v___x_287_, 0, lean_box(0));
lean_closure_set(v___x_287_, 1, v_inst_262_);
lean_closure_set(v___x_287_, 2, v_O_263_);
lean_closure_set(v___x_287_, 3, v_n_264_);
lean_closure_set(v___x_287_, 4, v_S_265_);
lean_closure_set(v___x_287_, 5, v_c_266_);
lean_inc_ref(v___x_287_);
lean_inc_ref(v___x_286_);
v___x_288_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_add___aux__1), 8, 6);
lean_closure_set(v___x_288_, 0, lean_box(0));
lean_closure_set(v___x_288_, 1, lean_box(0));
lean_closure_set(v___x_288_, 2, lean_box(0));
lean_closure_set(v___x_288_, 3, v_toAdd_271_);
lean_closure_set(v___x_288_, 4, v___x_286_);
lean_closure_set(v___x_288_, 5, v___x_287_);
v___x_289_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_sub___aux__1), 8, 6);
lean_closure_set(v___x_289_, 0, lean_box(0));
lean_closure_set(v___x_289_, 1, lean_box(0));
lean_closure_set(v___x_289_, 2, lean_box(0));
lean_closure_set(v___x_289_, 3, v_toSub_283_);
lean_closure_set(v___x_289_, 4, v___x_286_);
lean_closure_set(v___x_289_, 5, v___x_287_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_289_);
lean_ctor_set(v___x_275_, 0, v___x_288_);
v___x_291_ = v___x_275_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeU(lean_object* v_L_295_, lean_object* v_inst_296_, lean_object* v_O_297_, lean_object* v_n_298_, lean_object* v_S_299_, lean_object* v_c_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lp_tree_Formalism_UG_P_satakeU___redArg(v_inst_296_, v_O_297_, v_n_298_, v_S_299_, v_c_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeP___redArg(lean_object* v_inst_302_, lean_object* v_n_303_, lean_object* v_00_u03c3_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_toSemiring_307_; lean_object* v___x_308_; lean_object* v_toZero_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_327_; 
v___x_305_ = lp_mathlib_Field_toSemifield___redArg(v_inst_302_);
v___x_306_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_305_);
v_toSemiring_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_toSemiring_307_);
lean_dec_ref(v___x_306_);
v___x_308_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_307_);
v_toZero_309_ = lean_ctor_get(v___x_308_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_308_, 0);
lean_dec(v_unused_328_);
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_toZero_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v_toRing_314_; lean_object* v___x_315_; lean_object* v_toAddMonoidWithOne_316_; lean_object* v_toOne_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_313_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_302_);
v_toRing_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_toRing_314_);
lean_dec_ref(v___x_313_);
v___x_315_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_314_);
v_toAddMonoidWithOne_316_ = lean_ctor_get(v___x_315_, 1);
lean_inc_ref(v_toAddMonoidWithOne_316_);
lean_dec_ref(v___x_315_);
v_toOne_317_ = lean_ctor_get(v_toAddMonoidWithOne_316_, 2);
lean_inc_n(v_toOne_317_, 2);
lean_dec_ref(v_toAddMonoidWithOne_316_);
v___x_318_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_318_, 0, v_n_303_);
lean_inc_ref(v_00_u03c3_304_);
v___x_319_ = lp_mathlib_Equiv_toPEquiv___redArg(v_00_u03c3_304_);
lean_inc(v_toZero_309_);
lean_inc_ref(v___x_318_);
v___x_320_ = lean_alloc_closure((void*)(lp_mathlib_PEquiv_toMatrix), 9, 7);
lean_closure_set(v___x_320_, 0, lean_box(0));
lean_closure_set(v___x_320_, 1, lean_box(0));
lean_closure_set(v___x_320_, 2, lean_box(0));
lean_closure_set(v___x_320_, 3, v___x_318_);
lean_closure_set(v___x_320_, 4, v_toZero_309_);
lean_closure_set(v___x_320_, 5, v_toOne_317_);
lean_closure_set(v___x_320_, 6, v___x_319_);
v___x_321_ = lp_mathlib_Equiv_symm___redArg(v_00_u03c3_304_);
v___x_322_ = lp_mathlib_Equiv_toPEquiv___redArg(v___x_321_);
v___x_323_ = lean_alloc_closure((void*)(lp_mathlib_PEquiv_toMatrix), 9, 7);
lean_closure_set(v___x_323_, 0, lean_box(0));
lean_closure_set(v___x_323_, 1, lean_box(0));
lean_closure_set(v___x_323_, 2, lean_box(0));
lean_closure_set(v___x_323_, 3, v___x_318_);
lean_closure_set(v___x_323_, 4, v_toZero_309_);
lean_closure_set(v___x_323_, 5, v_toOne_317_);
lean_closure_set(v___x_323_, 6, v___x_322_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_323_);
lean_ctor_set(v___x_311_, 0, v___x_320_);
v___x_325_ = v___x_311_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeP(lean_object* v_L_329_, lean_object* v_inst_330_, lean_object* v_n_331_, lean_object* v_00_u03c3_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lp_tree_Formalism_UG_P_satakeP___redArg(v_inst_330_, v_n_331_, v_00_u03c3_332_);
return v___x_333_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementE(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
