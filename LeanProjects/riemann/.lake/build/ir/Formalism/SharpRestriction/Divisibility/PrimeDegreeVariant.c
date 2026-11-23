// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.PrincipalHermitianLattice public import Formalism.LocalRingCardinality.DataKap public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_finSumFinEquiv(lean_object*, lean_object*);
lean_object* lp_mathlib_finCongr(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_diagGL___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_degZ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_cutE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_cutE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_imgE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_imgE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_eigP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_eigP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__0(lean_object* v_toOne_1_, lean_object* v_x_2_){
_start:
{
lean_inc(v_toOne_1_);
return v_toOne_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__0___boxed(lean_object* v_toOne_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__0(v_toOne_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v_toOne_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__1(lean_object* v_toZero_6_, lean_object* v___x_7_, lean_object* v___f_8_, lean_object* v_A_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_toZero_6_);
v___x_12_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_12_, 0, lean_box(0));
lean_closure_set(v___x_12_, 1, lean_box(0));
lean_closure_set(v___x_12_, 2, lean_box(0));
lean_closure_set(v___x_12_, 3, v_toZero_6_);
v___x_13_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_13_, 0, v___x_7_);
v___x_14_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_14_, 0, lean_box(0));
lean_closure_set(v___x_14_, 1, lean_box(0));
lean_closure_set(v___x_14_, 2, v___x_13_);
lean_closure_set(v___x_14_, 3, v_toZero_6_);
lean_closure_set(v___x_14_, 4, v___f_8_);
lean_inc_ref(v___x_12_);
v___x_15_ = lp_mathlib_Matrix_fromBlocks___redArg(v_A_9_, v___x_12_, v___x_12_, v___x_14_, v___y_10_, v___y_11_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg(lean_object* v_inst_16_){
_start:
{
lean_object* v_toSemiring_17_; lean_object* v___x_18_; lean_object* v_toZero_19_; lean_object* v___x_20_; lean_object* v_toAddMonoidWithOne_21_; lean_object* v_toOne_22_; lean_object* v___x_23_; lean_object* v___f_24_; lean_object* v___f_25_; 
v_toSemiring_17_ = lean_ctor_get(v_inst_16_, 0);
lean_inc_ref(v_toSemiring_17_);
v___x_18_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_17_);
v_toZero_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_toZero_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_16_);
v_toAddMonoidWithOne_21_ = lean_ctor_get(v___x_20_, 1);
lean_inc_ref(v_toAddMonoidWithOne_21_);
lean_dec_ref(v___x_20_);
v_toOne_22_ = lean_ctor_get(v_toAddMonoidWithOne_21_, 2);
lean_inc(v_toOne_22_);
lean_dec_ref(v_toAddMonoidWithOne_21_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___f_24_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_24_, 0, v_toOne_22_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg___lam__1), 6, 3);
lean_closure_set(v___f_25_, 0, v_toZero_19_);
lean_closure_set(v___f_25_, 1, v___x_23_);
lean_closure_set(v___f_25_, 2, v___f_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom(lean_object* v_R_26_, lean_object* v_inst_27_, lean_object* v_n_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg(v_inst_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___boxed(lean_object* v_R_30_, lean_object* v_inst_31_, lean_object* v_n_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom(v_R_30_, v_inst_31_, v_n_32_);
lean_dec(v_n_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___redArg(lean_object* v_inst_34_, lean_object* v_n_35_, lean_object* v_N_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_toFun_43_; lean_object* v___x_44_; lean_object* v___f_45_; lean_object* v___f_46_; 
v___x_37_ = lean_unsigned_to_nat(1u);
lean_inc(v_n_35_);
v___x_38_ = lp_mathlib_finSumFinEquiv(v_n_35_, v___x_37_);
v___x_39_ = lean_nat_add(v_n_35_, v___x_37_);
lean_dec(v_n_35_);
v___x_40_ = lp_mathlib_finCongr(v___x_39_, v_N_36_, lean_box(0));
lean_dec(v___x_39_);
v___x_41_ = lp_mathlib_Equiv_trans___redArg(v___x_38_, v___x_40_);
lean_inc_ref(v___x_41_);
v___x_42_ = lp_mathlib_Matrix_reindex___redArg(v___x_41_, v___x_41_);
v_toFun_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_toFun_43_);
lean_dec_ref(v___x_42_);
v___x_44_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_blkHom___redArg(v_inst_34_);
v___f_45_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_45_, 0, v___x_44_);
lean_closure_set(v___f_45_, 1, v_toFun_43_);
v___f_46_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_46_, 0, v___f_45_);
return v___f_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___redArg___boxed(lean_object* v_inst_47_, lean_object* v_n_48_, lean_object* v_N_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___redArg(v_inst_47_, v_n_48_, v_N_49_);
lean_dec(v_N_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL(lean_object* v_R_51_, lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_N_54_, lean_object* v_h_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___redArg(v_inst_52_, v_n_53_, v_N_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL___boxed(lean_object* v_R_57_, lean_object* v_inst_58_, lean_object* v_n_59_, lean_object* v_N_60_, lean_object* v_h_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_embGL(v_R_57_, v_inst_58_, v_n_59_, v_N_60_, v_h_61_);
lean_dec(v_N_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg___lam__0(lean_object* v_N_63_, lean_object* v_inst_64_, lean_object* v_a_65_, lean_object* v_i_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_add(v_i_66_, v___x_67_);
v___x_69_ = lean_nat_dec_eq(v___x_68_, v_N_63_);
lean_dec(v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v_toSemiring_70_; lean_object* v_toMonoid_71_; lean_object* v___x_72_; lean_object* v_toOne_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_toSemiring_70_ = lean_ctor_get(v_inst_64_, 0);
v_toMonoid_71_ = lean_ctor_get(v_toSemiring_70_, 1);
v___x_72_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_71_);
v_toOne_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_72_, 1);
lean_dec(v_unused_81_);
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_toOne_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
lean_inc(v_toOne_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_toOne_73_);
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_toOne_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_toOne_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_inc_ref(v_a_65_);
return v_a_65_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg___lam__0___boxed(lean_object* v_N_82_, lean_object* v_inst_83_, lean_object* v_a_84_, lean_object* v_i_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg___lam__0(v_N_82_, v_inst_83_, v_a_84_, v_i_85_);
lean_dec(v_i_85_);
lean_dec_ref(v_a_84_);
lean_dec_ref(v_inst_83_);
lean_dec(v_N_82_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg(lean_object* v_inst_87_, lean_object* v_N_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; 
lean_inc_ref(v_inst_87_);
lean_inc(v_N_88_);
v___f_90_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_90_, 0, v_N_88_);
lean_closure_set(v___f_90_, 1, v_inst_87_);
lean_closure_set(v___f_90_, 2, v_a_89_);
v___x_91_ = lp_tree_Formalism_BasicNotions_diagGL___redArg(v_inst_87_, v_N_88_, v___f_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL(lean_object* v_R_92_, lean_object* v_inst_93_, lean_object* v_N_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_lastGL___redArg(v_inst_93_, v_N_94_, v_a_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum___lam__0(lean_object* v_l_97_, lean_object* v_i_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_1(v_l_97_, v_i_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum(lean_object* v_k_100_, lean_object* v_l_101_){
_start:
{
lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___f_102_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum___lam__0), 2, 1);
lean_closure_set(v___f_102_, 0, v_l_101_);
v___x_103_ = l_List_finRange(v_k_100_);
v___x_104_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_103_, v___f_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa___redArg(lean_object* v_lam_105_, lean_object* v_sg_106_, lean_object* v_i_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
lean_inc(v_i_107_);
v___x_108_ = lean_apply_1(v_sg_106_, v_i_107_);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_add(v_i_107_, v___x_109_);
lean_dec(v_i_107_);
v___x_111_ = lean_apply_1(v_lam_105_, v___x_110_);
v___x_112_ = lean_int_sub(v___x_108_, v___x_111_);
lean_dec(v___x_111_);
lean_dec(v___x_108_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa(lean_object* v_n_113_, lean_object* v_N_114_, lean_object* v_h_115_, lean_object* v_lam_116_, lean_object* v_sg_117_, lean_object* v_i_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa___redArg(v_lam_116_, v_sg_117_, v_i_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa___boxed(lean_object* v_n_120_, lean_object* v_N_121_, lean_object* v_h_122_, lean_object* v_lam_123_, lean_object* v_sg_124_, lean_object* v_i_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_aa(v_n_120_, v_N_121_, v_h_122_, v_lam_123_, v_sg_124_, v_i_125_);
lean_dec(v_N_121_);
lean_dec(v_n_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb___redArg(lean_object* v_lam_127_, lean_object* v_sg_128_, lean_object* v_i_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_inc(v_i_129_);
v___x_130_ = lean_apply_1(v_lam_127_, v_i_129_);
v___x_131_ = lean_apply_1(v_sg_128_, v_i_129_);
v___x_132_ = lean_int_sub(v___x_130_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb(lean_object* v_n_133_, lean_object* v_N_134_, lean_object* v_h_135_, lean_object* v_lam_136_, lean_object* v_sg_137_, lean_object* v_i_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb___redArg(v_lam_136_, v_sg_137_, v_i_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb___boxed(lean_object* v_n_140_, lean_object* v_N_141_, lean_object* v_h_142_, lean_object* v_lam_143_, lean_object* v_sg_144_, lean_object* v_i_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_bb(v_n_140_, v_N_141_, v_h_142_, v_lam_143_, v_sg_144_, v_i_145_);
lean_dec(v_N_141_);
lean_dec(v_n_140_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg___lam__0(lean_object* v_sg_147_, lean_object* v_lam_148_, lean_object* v_i_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_inc(v_i_149_);
v___x_150_ = lean_apply_1(v_sg_147_, v_i_149_);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_i_149_, v___x_151_);
lean_dec(v_i_149_);
v___x_153_ = lean_apply_1(v_lam_148_, v___x_152_);
v___x_154_ = lean_int_sub(v___x_150_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_150_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg(lean_object* v_n_155_, lean_object* v_lam_156_, lean_object* v_sg_157_){
_start:
{
lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___f_158_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_158_, 0, v_sg_157_);
lean_closure_set(v___f_158_, 1, v_lam_156_);
v___x_159_ = l_List_finRange(v_n_155_);
v___x_160_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_159_, v___f_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0(lean_object* v_n_161_, lean_object* v_N_162_, lean_object* v_h_163_, lean_object* v_lam_164_, lean_object* v_sg_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg(v_n_161_, v_lam_164_, v_sg_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___boxed(lean_object* v_n_167_, lean_object* v_N_168_, lean_object* v_h_169_, lean_object* v_lam_170_, lean_object* v_sg_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0(v_n_167_, v_N_168_, v_h_169_, v_lam_170_, v_sg_171_);
lean_dec(v_N_168_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___redArg___lam__0(lean_object* v_lam_173_, lean_object* v_n_174_, lean_object* v_sg_175_, lean_object* v_i_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
lean_inc_ref_n(v_lam_173_, 2);
lean_inc(v_i_176_);
v___x_177_ = lean_apply_1(v_lam_173_, v_i_176_);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_i_176_, v___x_178_);
lean_dec(v_i_176_);
v___x_180_ = lean_apply_1(v_lam_173_, v___x_179_);
v___x_181_ = lean_int_sub(v___x_177_, v___x_180_);
lean_dec(v___x_180_);
lean_dec(v___x_177_);
v___x_182_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D0___redArg(v_n_174_, v_lam_173_, v_sg_175_);
v___x_183_ = lean_int_dec_le(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_dec(v___x_181_);
return v___x_182_;
}
else
{
lean_dec(v___x_182_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___redArg(lean_object* v_n_184_, lean_object* v_lam_185_, lean_object* v_sg_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v_n_184_);
v___f_187_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___redArg___lam__0), 4, 3);
lean_closure_set(v___f_187_, 0, v_lam_185_);
lean_closure_set(v___f_187_, 1, v_n_184_);
lean_closure_set(v___f_187_, 2, v_sg_186_);
v___x_188_ = l_List_finRange(v_n_184_);
v___x_189_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_188_, v___f_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1(lean_object* v_n_190_, lean_object* v_N_191_, lean_object* v_h_192_, lean_object* v_lam_193_, lean_object* v_sg_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___redArg(v_n_190_, v_lam_193_, v_sg_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1___boxed(lean_object* v_n_196_, lean_object* v_N_197_, lean_object* v_h_198_, lean_object* v_lam_199_, lean_object* v_sg_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_D1(v_n_196_, v_N_197_, v_h_198_, v_lam_199_, v_sg_200_);
lean_dec(v_N_197_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_degZ(lean_object* v_n_202_, lean_object* v_N_203_, lean_object* v_lam_204_, lean_object* v_sg_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum(v_N_203_, v_lam_204_);
v___x_207_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_wsum(v_n_202_, v_sg_205_);
v___x_208_ = lean_int_sub(v___x_206_, v___x_207_);
lean_dec(v___x_207_);
lean_dec(v___x_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___redArg(lean_object* v_N_209_, lean_object* v_i_210_, lean_object* v_p_211_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_nat_dec_eq(v_p_211_, v_i_210_);
if (v___x_212_ == 0)
{
lean_inc(v_p_211_);
return v_p_211_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_sub(v_N_209_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___redArg___boxed(lean_object* v_N_215_, lean_object* v_i_216_, lean_object* v_p_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___redArg(v_N_215_, v_i_216_, v_p_217_);
lean_dec(v_p_217_);
lean_dec(v_i_216_);
lean_dec(v_N_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ(lean_object* v_n_219_, lean_object* v_N_220_, lean_object* v_h_221_, lean_object* v_i_222_, lean_object* v_p_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___redArg(v_N_220_, v_i_222_, v_p_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ___boxed(lean_object* v_n_225_, lean_object* v_N_226_, lean_object* v_h_227_, lean_object* v_i_228_, lean_object* v_p_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_rowsZ(v_n_225_, v_N_226_, v_h_227_, v_i_228_, v_p_229_);
lean_dec(v_p_229_);
lean_dec(v_i_228_);
lean_dec(v_N_226_);
lean_dec(v_n_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_cutE(lean_object* v_K_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_A_235_, lean_object* v_e_236_, lean_object* v_M_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_cutE___boxed(lean_object* v_K_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_A_243_, lean_object* v_e_244_, lean_object* v_M_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_cutE(v_K_239_, v_inst_240_, v_inst_241_, v_inst_242_, v_A_243_, v_e_244_, v_M_245_);
lean_dec(v_e_244_);
lean_dec_ref(v_A_243_);
lean_dec(v_inst_242_);
lean_dec_ref(v_inst_240_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_imgE(lean_object* v_K_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_A_251_, lean_object* v_e_252_, lean_object* v_M_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_imgE___boxed(lean_object* v_K_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_A_259_, lean_object* v_e_260_, lean_object* v_M_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_imgE(v_K_255_, v_inst_256_, v_inst_257_, v_inst_258_, v_A_259_, v_e_260_, v_M_261_);
lean_dec(v_e_260_);
lean_dec_ref(v_A_259_);
lean_dec(v_inst_258_);
lean_dec_ref(v_inst_256_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_eigP(lean_object* v_K_263_, lean_object* v_inst_264_, lean_object* v_00_u03c3_265_, lean_object* v_G_266_, lean_object* v_inst_267_, lean_object* v_P_268_, lean_object* v_V_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_00_u03c1_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_eigP___boxed(lean_object* v_K_274_, lean_object* v_inst_275_, lean_object* v_00_u03c3_276_, lean_object* v_G_277_, lean_object* v_inst_278_, lean_object* v_P_279_, lean_object* v_V_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_00_u03c1_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_eigP(v_K_274_, v_inst_275_, v_00_u03c3_276_, v_G_277_, v_inst_278_, v_P_279_, v_V_280_, v_inst_281_, v_inst_282_, v_00_u03c1_283_);
lean_dec(v_00_u03c1_283_);
lean_dec(v_inst_282_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_P_279_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_00_u03c3_276_);
lean_dec_ref(v_inst_275_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___redArg(lean_object* v_Y_285_){
_start:
{
lean_object* v_sK_286_; lean_object* v_RR_287_; 
v_sK_286_ = lean_ctor_get(v_Y_285_, 5);
v_RR_287_ = lean_ctor_get(v_sK_286_, 10);
lean_inc_ref(v_RR_287_);
return v_RR_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___redArg___boxed(lean_object* v_Y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___redArg(v_Y_288_);
lean_dec_ref(v_Y_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK(lean_object* v_D_290_, lean_object* v_X_291_, lean_object* v_Y_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___redArg(v_Y_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK___boxed(lean_object* v_D_294_, lean_object* v_X_295_, lean_object* v_Y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_RK(v_D_294_, v_X_295_, v_Y_296_);
lean_dec_ref(v_Y_296_);
lean_dec_ref(v_X_295_);
lean_dec_ref(v_D_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___redArg(lean_object* v_D_298_, lean_object* v_Y_299_){
_start:
{
lean_object* v_nexp_300_; lean_object* v_U_301_; lean_object* v_psi0_302_; lean_object* v___x_303_; 
v_nexp_300_ = lean_ctor_get(v_D_298_, 45);
v_U_301_ = lean_ctor_get(v_nexp_300_, 4);
lean_inc(v_U_301_);
v_psi0_302_ = lean_ctor_get(v_Y_299_, 1);
lean_inc_ref(v_psi0_302_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_U_301_);
lean_ctor_set(v___x_303_, 1, v_psi0_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___redArg___boxed(lean_object* v_D_304_, lean_object* v_Y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___redArg(v_D_304_, v_Y_305_);
lean_dec_ref(v_Y_305_);
lean_dec_ref(v_D_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0(lean_object* v_D_307_, lean_object* v_X_308_, lean_object* v_Y_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___redArg(v_D_307_, v_Y_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0___boxed(lean_object* v_D_311_, lean_object* v_X_312_, lean_object* v_Y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = lp_tree_Formalism_MainNotions_PrimeDegreeVariant_Prov_P0(v_D_311_, v_X_312_, v_Y_313_);
lean_dec_ref(v_Y_313_);
lean_dec_ref(v_X_312_);
lean_dec_ref(v_D_311_);
return v_res_314_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__0(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_unsigned_to_nat(2u);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_nat_mod(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__1(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(2u);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_mod(v___x_319_, v___x_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar(lean_object* v_D_321_){
_start:
{
lean_object* v_host_322_; lean_object* v_R_323_; lean_object* v_g_324_; lean_object* v_k_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_host_322_ = lean_ctor_get(v_D_321_, 1);
lean_inc_ref(v_host_322_);
v_R_323_ = lean_ctor_get(v_D_321_, 0);
lean_inc_ref(v_R_323_);
lean_dec_ref(v_D_321_);
v_g_324_ = lean_ctor_get(v_host_322_, 6);
lean_inc_ref_n(v_g_324_, 2);
lean_dec_ref(v_host_322_);
v_k_325_ = lean_ctor_get(v_R_323_, 1);
lean_inc(v_k_325_);
v___x_326_ = lean_obj_once(&lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__0, &lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__0_once, _init_lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__0);
v___x_327_ = lean_apply_1(v_g_324_, v___x_326_);
v___x_328_ = lean_obj_once(&lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__1, &lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__1_once, _init_lp_tree_Formalism_MainNotions_PrimeDegreeVariant_nbar___closed__1);
v___x_329_ = lean_apply_1(v_g_324_, v___x_328_);
v___x_330_ = lean_nat_mul(v___x_327_, v___x_329_);
lean_dec(v___x_329_);
lean_dec(v___x_327_);
v___x_331_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_330_);
v___x_332_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_323_);
lean_dec_ref(v_R_323_);
v___x_333_ = lean_nat_mul(v___x_332_, v_k_325_);
lean_dec(v_k_325_);
lean_dec(v___x_332_);
v___x_334_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_333_, v___x_331_);
lean_dec(v___x_333_);
return v___x_334_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKap(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_ArithmeticCylinders(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_PrimeDegreeVariant(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_ArithmeticCylinders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
