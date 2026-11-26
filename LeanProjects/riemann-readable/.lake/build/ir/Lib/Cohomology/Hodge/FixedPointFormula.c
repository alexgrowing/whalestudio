// Lean compiler output
// Module: Lib.Cohomology.Hodge.FixedPointFormula
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.Defs public import Lib.Cohomology.Hodge.DiagonalClass public import Lib.Cohomology.Hodge.Kunneth public import Lib.General.Algebra.MultivariatePolynomials
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
lean_object* lp_mathlib_Algebra_id___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toOppositeModule___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_instSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_ring___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_instAlgebra___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Module_Dual_eval___redArg();
lean_object* lp_mathlib_TrivSqZeroExt_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_CategoryTheory_types;
extern lean_object* lp_mathlib_CategoryTheory_typesCartesianMonoidalCategory;
lean_object* lp_mathlib_CategoryTheory_Functor_cartesianMonoidalCategory___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_HodgeTest_sqZeroExt___redArg();
lean_object* lp_mathlib_CategoryTheory_Functor_comp___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_HodgeTest_scaleModule___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_whiskerLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_CartesianMonoidalCategory_lift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jetTangent___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jetTangent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jetTangent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_scaledGraph___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_scaledGraph___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_scaledGraph___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_scaledGraph___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_scaledGraph___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_scaledGraph(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_scaledGraph___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jetTangent___redArg(lean_object* v_inst_1_, lean_object* v_W_2_, lean_object* v_v_3_, lean_object* v_00_u03c6_4_){
_start:
{
lean_object* v_toCommRing_5_; lean_object* v___x_6_; lean_object* v_toCommSemiring_7_; lean_object* v___x_8_; lean_object* v_toRing_9_; lean_object* v___x_10_; lean_object* v_toAddCommMonoid_11_; lean_object* v_toSemiring_12_; lean_object* v_map_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_38_; 
v_toCommRing_5_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toCommRing_5_);
v___x_6_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v_toCommSemiring_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_toCommSemiring_7_);
lean_dec_ref(v___x_6_);
v___x_8_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v_toRing_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_toRing_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_9_);
lean_dec_ref(v_toRing_9_);
v_toAddCommMonoid_11_ = lean_ctor_get(v_toCommSemiring_7_, 0);
lean_inc_ref(v_toAddCommMonoid_11_);
v_toSemiring_12_ = lean_ctor_get(v_toCommRing_5_, 0);
v_map_13_ = lean_ctor_get(v_W_2_, 1);
v_isSharedCheck_38_ = !lean_is_exclusive(v_W_2_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; 
v_unused_39_ = lean_ctor_get(v_W_2_, 0);
lean_dec(v_unused_39_);
v___x_15_ = v_W_2_;
v_isShared_16_ = v_isSharedCheck_38_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_map_13_);
lean_dec(v_W_2_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_38_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_17_ = lp_mathlib_Semiring_toModule___redArg(v_toCommSemiring_7_);
v___x_18_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_12_);
v___x_19_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toSemiring_12_);
v___x_20_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toCommSemiring_7_);
lean_inc_ref(v___x_10_);
v___x_21_ = lp_mathlib_LinearMap_addCommGroup___redArg(v___x_10_);
lean_inc(v___x_18_);
v___f_22_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_22_, 0, v___x_18_);
lean_inc(v___x_19_);
v___f_23_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_23_, 0, v___x_19_);
lean_inc_ref(v_toCommRing_5_);
v___x_24_ = lp_mathlib_TrivSqZeroExt_ring___redArg(v_toCommRing_5_, v___x_21_, v___f_22_, v___f_23_);
lean_inc_ref(v_toAddCommMonoid_11_);
v___x_25_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddCommMonoid_11_);
lean_inc(v___x_17_);
v___f_26_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_26_, 0, v___x_17_);
lean_inc_ref(v_toCommSemiring_7_);
v___x_27_ = lp_mathlib_TrivSqZeroExt_instAlgebra___redArg(v_toCommSemiring_7_, v___x_25_, v___f_26_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___x_27_);
lean_ctor_set(v___x_15_, 0, v___x_24_);
v___x_29_ = v___x_15_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_27_);
v___x_29_ = v_reuseFailAlloc_37_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_84__overap_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_30_ = lp_mathlib_TrivSqZeroExt_ring___redArg(v_toCommRing_5_, v___x_10_, v___x_18_, v___x_19_);
lean_inc(v___x_17_);
lean_inc_ref(v_toCommSemiring_7_);
v___x_31_ = lp_mathlib_TrivSqZeroExt_instAlgebra___redArg(v_toCommSemiring_7_, v_toAddCommMonoid_11_, v___x_17_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_84__overap_33_ = lp_mathlib_Module_Dual_eval___redArg();
v___x_34_ = lean_apply_1(v___x_84__overap_33_, v_00_u03c6_4_);
v___x_35_ = lp_mathlib_TrivSqZeroExt_map___redArg(v_toCommSemiring_7_, v___x_25_, v_toAddCommMonoid_11_, v___x_17_, v___x_20_, v___x_34_);
v___x_36_ = lean_apply_4(v_map_13_, v___x_29_, v___x_32_, v___x_35_, v_v_3_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jetTangent(lean_object* v_k_40_, lean_object* v_inst_41_, lean_object* v_W_42_, lean_object* v_T_43_, lean_object* v_v_44_, lean_object* v_00_u03c6_45_){
_start:
{
lean_object* v_toCommRing_46_; lean_object* v___x_47_; lean_object* v_toCommSemiring_48_; lean_object* v___x_49_; lean_object* v_toRing_50_; lean_object* v___x_51_; lean_object* v_toAddCommMonoid_52_; lean_object* v_toSemiring_53_; lean_object* v_map_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_79_; 
v_toCommRing_46_ = lean_ctor_get(v_inst_41_, 0);
lean_inc_ref(v_toCommRing_46_);
v___x_47_ = lp_mathlib_Field_toSemifield___redArg(v_inst_41_);
v_toCommSemiring_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_toCommSemiring_48_);
lean_dec_ref(v___x_47_);
v___x_49_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_41_);
v_toRing_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_toRing_50_);
lean_dec_ref(v___x_49_);
v___x_51_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_50_);
lean_dec_ref(v_toRing_50_);
v_toAddCommMonoid_52_ = lean_ctor_get(v_toCommSemiring_48_, 0);
lean_inc_ref(v_toAddCommMonoid_52_);
v_toSemiring_53_ = lean_ctor_get(v_toCommRing_46_, 0);
v_map_54_ = lean_ctor_get(v_W_42_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_W_42_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_W_42_, 0);
lean_dec(v_unused_80_);
v___x_56_ = v_W_42_;
v_isShared_57_ = v_isSharedCheck_79_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_map_54_);
lean_dec(v_W_42_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_79_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_58_ = lp_mathlib_Semiring_toModule___redArg(v_toCommSemiring_48_);
v___x_59_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_53_);
v___x_60_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toSemiring_53_);
v___x_61_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toCommSemiring_48_);
lean_inc_ref(v___x_51_);
v___x_62_ = lp_mathlib_LinearMap_addCommGroup___redArg(v___x_51_);
lean_inc(v___x_59_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_63_, 0, v___x_59_);
lean_inc(v___x_60_);
v___f_64_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_64_, 0, v___x_60_);
lean_inc_ref(v_toCommRing_46_);
v___x_65_ = lp_mathlib_TrivSqZeroExt_ring___redArg(v_toCommRing_46_, v___x_62_, v___f_63_, v___f_64_);
lean_inc_ref(v_toAddCommMonoid_52_);
v___x_66_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddCommMonoid_52_);
lean_inc(v___x_58_);
v___f_67_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_67_, 0, v___x_58_);
lean_inc_ref(v_toCommSemiring_48_);
v___x_68_ = lp_mathlib_TrivSqZeroExt_instAlgebra___redArg(v_toCommSemiring_48_, v___x_66_, v___f_67_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___x_68_);
lean_ctor_set(v___x_56_, 0, v___x_65_);
v___x_70_ = v___x_56_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_78_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_130__overap_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_71_ = lp_mathlib_TrivSqZeroExt_ring___redArg(v_toCommRing_46_, v___x_51_, v___x_59_, v___x_60_);
lean_inc(v___x_58_);
lean_inc_ref(v_toCommSemiring_48_);
v___x_72_ = lp_mathlib_TrivSqZeroExt_instAlgebra___redArg(v_toCommSemiring_48_, v_toAddCommMonoid_52_, v___x_58_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_130__overap_74_ = lp_mathlib_Module_Dual_eval___redArg();
v___x_75_ = lean_apply_1(v___x_130__overap_74_, v_00_u03c6_45_);
v___x_76_ = lp_mathlib_TrivSqZeroExt_map___redArg(v_toCommSemiring_48_, v___x_66_, v_toAddCommMonoid_52_, v___x_58_, v___x_61_, v___x_75_);
v___x_77_ = lean_apply_4(v_map_54_, v___x_70_, v___x_73_, v___x_76_, v_v_44_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_jetTangent___boxed(lean_object* v_k_81_, lean_object* v_inst_82_, lean_object* v_W_83_, lean_object* v_T_84_, lean_object* v_v_85_, lean_object* v_00_u03c6_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_GRH_New_Variety_jetTangent(v_k_81_, v_inst_82_, v_W_83_, v_T_84_, v_v_85_, v_00_u03c6_86_);
lean_dec_ref(v_T_84_);
return v_res_87_;
}
}
static lean_object* _init_lp_GRH_New_Variety_scaledGraph___redArg___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lp_mathlib_CategoryTheory_typesCartesianMonoidalCategory;
v___x_89_ = lp_mathlib_CategoryTheory_types;
v___x_90_ = lp_mathlib_CategoryTheory_Functor_cartesianMonoidalCategory___redArg(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_New_Variety_scaledGraph___redArg___closed__1(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_GRH_New_Variety_HodgeTest_sqZeroExt___redArg();
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_scaledGraph___redArg(lean_object* v_W_92_, lean_object* v_X_93_, lean_object* v_t_94_, lean_object* v_u_95_, lean_object* v_c_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___x_106_; 
v___x_97_ = lp_mathlib_CategoryTheory_types;
v___x_98_ = lean_obj_once(&lp_GRH_New_Variety_scaledGraph___redArg___closed__0, &lp_GRH_New_Variety_scaledGraph___redArg___closed__0_once, _init_lp_GRH_New_Variety_scaledGraph___redArg___closed__0);
v___x_99_ = lean_obj_once(&lp_GRH_New_Variety_scaledGraph___redArg___closed__1, &lp_GRH_New_Variety_scaledGraph___redArg___closed__1_once, _init_lp_GRH_New_Variety_scaledGraph___redArg___closed__1);
v___x_100_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_99_, v_W_92_);
v___x_101_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_99_, v_X_93_);
lean_inc_ref_n(v___x_100_, 3);
v___x_102_ = lp_GRH_New_Variety_HodgeTest_scaleModule___redArg(v_t_94_, v___x_100_);
v___f_103_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_Functor_whiskerLeft___redArg___lam__0), 3, 2);
lean_closure_set(v___f_103_, 0, v___x_99_);
lean_closure_set(v___f_103_, 1, v_u_95_);
lean_inc_ref_n(v___x_101_, 2);
v___f_104_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0), 7, 6);
lean_closure_set(v___f_104_, 0, v___x_97_);
lean_closure_set(v___f_104_, 1, v___x_100_);
lean_closure_set(v___f_104_, 2, v___x_100_);
lean_closure_set(v___f_104_, 3, v___x_101_);
lean_closure_set(v___f_104_, 4, v___x_102_);
lean_closure_set(v___f_104_, 5, v___f_103_);
v___f_105_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_Functor_whiskerLeft___redArg___lam__0), 3, 2);
lean_closure_set(v___f_105_, 0, v___x_99_);
lean_closure_set(v___f_105_, 1, v_c_96_);
v___x_106_ = lp_mathlib_CategoryTheory_CartesianMonoidalCategory_lift___redArg(v___x_98_, v___x_100_, v___x_101_, v___x_101_, v___f_104_, v___f_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_scaledGraph(lean_object* v_k_107_, lean_object* v_inst_108_, lean_object* v_W_109_, lean_object* v_X_110_, lean_object* v_t_111_, lean_object* v_u_112_, lean_object* v_c_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lp_GRH_New_Variety_scaledGraph___redArg(v_W_109_, v_X_110_, v_t_111_, v_u_112_, v_c_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_scaledGraph___boxed(lean_object* v_k_115_, lean_object* v_inst_116_, lean_object* v_W_117_, lean_object* v_X_118_, lean_object* v_t_119_, lean_object* v_u_120_, lean_object* v_c_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_GRH_New_Variety_scaledGraph(v_k_115_, v_inst_116_, v_W_117_, v_X_118_, v_t_119_, v_u_120_, v_c_121_);
lean_dec_ref(v_inst_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___redArg___lam__0(lean_object* v_X_123_, lean_object* v_toCommRing_124_, lean_object* v___x_125_, lean_object* v_z_126_, lean_object* v_A_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_algebra_129_; lean_object* v_map_130_; lean_object* v_algebraMap_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_algebra_129_ = lean_ctor_get(v_A_127_, 1);
lean_inc_ref(v_algebra_129_);
v_map_130_ = lean_ctor_get(v_X_123_, 1);
lean_inc(v_map_130_);
lean_dec_ref(v_X_123_);
v_algebraMap_131_ = lean_ctor_get(v_algebra_129_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_algebra_129_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v_algebra_129_, 0);
lean_dec(v_unused_140_);
v___x_133_ = v_algebra_129_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_algebraMap_131_);
lean_dec(v_algebra_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_125_);
lean_ctor_set(v___x_133_, 0, v_toCommRing_124_);
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_toCommRing_124_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_125_);
v___x_136_ = v_reuseFailAlloc_138_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; 
v___x_137_ = lean_apply_4(v_map_130_, v___x_136_, v_A_127_, v_algebraMap_131_, v_z_126_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___redArg___lam__0___boxed(lean_object* v_X_141_, lean_object* v_toCommRing_142_, lean_object* v___x_143_, lean_object* v_z_144_, lean_object* v_A_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_GRH_New_Variety_constMap___redArg___lam__0(v_X_141_, v_toCommRing_142_, v___x_143_, v_z_144_, v_A_145_, v___y_146_);
lean_dec(v___y_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___redArg(lean_object* v_inst_148_, lean_object* v_X_149_, lean_object* v_z_150_){
_start:
{
lean_object* v_toCommRing_151_; lean_object* v_toSemiring_152_; lean_object* v___x_153_; lean_object* v___f_154_; 
v_toCommRing_151_ = lean_ctor_get(v_inst_148_, 0);
lean_inc_ref(v_toCommRing_151_);
lean_dec_ref(v_inst_148_);
v_toSemiring_152_ = lean_ctor_get(v_toCommRing_151_, 0);
lean_inc_ref(v_toSemiring_152_);
v___x_153_ = lp_mathlib_Algebra_id___redArg(v_toSemiring_152_);
v___f_154_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_constMap___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_154_, 0, v_X_149_);
lean_closure_set(v___f_154_, 1, v_toCommRing_151_);
lean_closure_set(v___f_154_, 2, v___x_153_);
lean_closure_set(v___f_154_, 3, v_z_150_);
return v___f_154_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap(lean_object* v_k_155_, lean_object* v_inst_156_, lean_object* v_W_157_, lean_object* v_X_158_, lean_object* v_z_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lp_GRH_New_Variety_constMap___redArg(v_inst_156_, v_X_158_, v_z_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_constMap___boxed(lean_object* v_k_161_, lean_object* v_inst_162_, lean_object* v_W_163_, lean_object* v_X_164_, lean_object* v_z_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_GRH_New_Variety_constMap(v_k_161_, v_inst_162_, v_W_163_, v_X_164_, v_z_165_);
lean_dec_ref(v_W_163_);
return v_res_166_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Hodge_DiagonalClass(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Hodge_Kunneth(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_Hodge_FixedPointFormula(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_Hodge_DiagonalClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_Hodge_Kunneth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
