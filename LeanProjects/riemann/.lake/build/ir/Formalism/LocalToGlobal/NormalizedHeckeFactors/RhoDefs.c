// Lean compiler output
// Module: Formalism.LocalToGlobal.NormalizedHeckeFactors.RhoDefs
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
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
lean_object* lp_mathlib_finCongr(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_scalar___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL___redArg(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v_toFun_5_; lean_object* v___f_6_; 
v___x_3_ = lp_mathlib_finCongr(v_a_1_, v_b_2_, lean_box(0));
lean_inc_ref(v___x_3_);
v___x_4_ = lp_mathlib_Matrix_reindex___redArg(v___x_3_, v___x_3_);
v_toFun_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toFun_5_);
lean_dec_ref(v___x_4_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_toFun_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL___redArg___boxed(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_L2_NR_reindexGL___redArg(v_a_7_, v_b_8_);
lean_dec(v_b_8_);
lean_dec(v_a_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL(lean_object* v_R_10_, lean_object* v_inst_11_, lean_object* v_a_12_, lean_object* v_b_13_, lean_object* v_h_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_tree_Formalism_L2_NR_reindexGL___redArg(v_a_12_, v_b_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_reindexGL___boxed(lean_object* v_R_16_, lean_object* v_inst_17_, lean_object* v_a_18_, lean_object* v_b_19_, lean_object* v_h_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_NR_reindexGL(v_R_16_, v_inst_17_, v_a_18_, v_b_19_, v_h_20_);
lean_dec(v_b_19_);
lean_dec(v_a_18_);
lean_dec_ref(v_inst_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__0(lean_object* v_inv_22_, lean_object* v___y_23_, lean_object* v_j_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_apply_2(v_inv_22_, v_j_24_, v___y_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__1(lean_object* v_inv_26_, lean_object* v___y_27_, lean_object* v_j_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_2(v_inv_26_, v___y_27_, v_j_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__2(lean_object* v_inv_30_, lean_object* v_inv_31_, lean_object* v___x_32_, lean_object* v_toMul_33_, lean_object* v_toAddCommMonoid_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v___f_37_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__0), 3, 2);
lean_closure_set(v___f_37_, 0, v_inv_30_);
lean_closure_set(v___f_37_, 1, v___y_36_);
v___f_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__1), 3, 2);
lean_closure_set(v___f_38_, 0, v_inv_31_);
lean_closure_set(v___f_38_, 1, v___y_35_);
v___x_39_ = lp_mathlib_dotProduct___redArg(v___x_32_, v_toMul_33_, v_toAddCommMonoid_34_, v___f_38_, v___f_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__2___boxed(lean_object* v_inv_40_, lean_object* v_inv_41_, lean_object* v___x_42_, lean_object* v_toMul_43_, lean_object* v_toAddCommMonoid_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_L2_NR_twistRep___redArg___lam__2(v_inv_40_, v_inv_41_, v___x_42_, v_toMul_43_, v_toAddCommMonoid_44_, v___y_45_, v___y_46_);
lean_dec_ref(v_toAddCommMonoid_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__3(lean_object* v_val_48_, lean_object* v___y_49_, lean_object* v_j_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_apply_2(v_val_48_, v_j_50_, v___y_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__4(lean_object* v_val_52_, lean_object* v___y_53_, lean_object* v_j_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_apply_2(v_val_52_, v___y_53_, v_j_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__5(lean_object* v_val_56_, lean_object* v_val_57_, lean_object* v___x_58_, lean_object* v_toMul_59_, lean_object* v_toAddCommMonoid_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v___f_63_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__3), 3, 2);
lean_closure_set(v___f_63_, 0, v_val_56_);
lean_closure_set(v___f_63_, 1, v___y_62_);
v___f_64_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__4), 3, 2);
lean_closure_set(v___f_64_, 0, v_val_57_);
lean_closure_set(v___f_64_, 1, v___y_61_);
v___x_65_ = lp_mathlib_dotProduct___redArg(v___x_58_, v_toMul_59_, v_toAddCommMonoid_60_, v___f_64_, v___f_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__5___boxed(lean_object* v_val_66_, lean_object* v_val_67_, lean_object* v___x_68_, lean_object* v_toMul_69_, lean_object* v_toAddCommMonoid_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_tree_Formalism_L2_NR_twistRep___redArg___lam__5(v_val_66_, v_val_67_, v___x_68_, v_toMul_69_, v_toAddCommMonoid_70_, v___y_71_, v___y_72_);
lean_dec_ref(v_toAddCommMonoid_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6(lean_object* v_toSemiring_75_, lean_object* v___x_76_, lean_object* v_00_u03c7_77_, lean_object* v_00_u03c1_78_, lean_object* v___x_79_, lean_object* v_g_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_val_86_; lean_object* v_inv_87_; lean_object* v___x_88_; lean_object* v_val_89_; lean_object* v_inv_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_103_; 
lean_inc_ref(v_toSemiring_75_);
v___x_81_ = lp_mathlib_Matrix_scalar___redArg(v_toSemiring_75_, v___x_76_);
v___f_82_ = ((lean_object*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6___closed__0));
v___f_83_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_83_, 0, v___f_82_);
lean_closure_set(v___f_83_, 1, v___x_81_);
lean_inc(v_g_80_);
v___x_84_ = lean_apply_1(v_00_u03c7_77_, v_g_80_);
v___x_85_ = lp_mathlib_Units_map___redArg___lam__0(v___f_83_, v___x_84_);
v_val_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_val_86_);
v_inv_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_inv_87_);
lean_dec_ref(v___x_85_);
v___x_88_ = lean_apply_1(v_00_u03c1_78_, v_g_80_);
v_val_89_ = lean_ctor_get(v___x_88_, 0);
v_inv_90_ = lean_ctor_get(v___x_88_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_103_ == 0)
{
v___x_92_ = v___x_88_;
v_isShared_93_ = v_isSharedCheck_103_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_inv_90_);
lean_inc(v_val_89_);
lean_dec(v___x_88_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_103_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v_toAddCommMonoid_95_; lean_object* v___x_96_; lean_object* v_toMul_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_101_; 
v___x_94_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_75_);
lean_dec_ref(v_toSemiring_75_);
v_toAddCommMonoid_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref_n(v_toAddCommMonoid_95_, 2);
v___x_96_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_94_);
v_toMul_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_n(v_toMul_97_, 2);
lean_dec_ref(v___x_96_);
lean_inc(v___x_79_);
v___f_98_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_98_, 0, v_inv_87_);
lean_closure_set(v___f_98_, 1, v_inv_90_);
lean_closure_set(v___f_98_, 2, v___x_79_);
lean_closure_set(v___f_98_, 3, v_toMul_97_);
lean_closure_set(v___f_98_, 4, v_toAddCommMonoid_95_);
v___f_99_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_99_, 0, v_val_89_);
lean_closure_set(v___f_99_, 1, v_val_86_);
lean_closure_set(v___f_99_, 2, v___x_79_);
lean_closure_set(v___f_99_, 3, v_toMul_97_);
lean_closure_set(v___f_99_, 4, v_toAddCommMonoid_95_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___f_98_);
lean_ctor_set(v___x_92_, 0, v___f_99_);
v___x_101_ = v___x_92_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___f_99_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___f_98_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___redArg(lean_object* v_inst_104_, lean_object* v_n_105_, lean_object* v_00_u03c1_106_, lean_object* v_00_u03c7_107_){
_start:
{
lean_object* v_toSemiring_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___f_111_; 
v_toSemiring_108_ = lean_ctor_get(v_inst_104_, 0);
lean_inc_ref(v_toSemiring_108_);
lean_dec_ref(v_inst_104_);
lean_inc(v_n_105_);
v___x_109_ = l_List_finRange(v_n_105_);
v___x_110_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_110_, 0, v_n_105_);
v___f_111_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NR_twistRep___redArg___lam__6), 6, 5);
lean_closure_set(v___f_111_, 0, v_toSemiring_108_);
lean_closure_set(v___f_111_, 1, v___x_110_);
lean_closure_set(v___f_111_, 2, v_00_u03c7_107_);
lean_closure_set(v___f_111_, 3, v_00_u03c1_106_);
lean_closure_set(v___f_111_, 4, v___x_109_);
return v___f_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep(lean_object* v_00_u0393_112_, lean_object* v_K_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_n_116_, lean_object* v_00_u03c1_117_, lean_object* v_00_u03c7_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_tree_Formalism_L2_NR_twistRep___redArg(v_inst_115_, v_n_116_, v_00_u03c1_117_, v_00_u03c7_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NR_twistRep___boxed(lean_object* v_00_u0393_120_, lean_object* v_K_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_n_124_, lean_object* v_00_u03c1_125_, lean_object* v_00_u03c7_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_tree_Formalism_L2_NR_twistRep(v_00_u0393_120_, v_K_121_, v_inst_122_, v_inst_123_, v_n_124_, v_00_u03c1_125_, v_00_u03c7_126_);
lean_dec_ref(v_inst_122_);
return v_res_127_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_NGalTied(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_SumRepresentations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_RhoDefs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_NGalTied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_SumRepresentations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
