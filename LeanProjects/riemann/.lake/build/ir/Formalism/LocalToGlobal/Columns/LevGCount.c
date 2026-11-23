// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.LevGCount
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter public import Formalism.GL3MeanSquares.HookFormulaTorsion.DimensionMassJointBound
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
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_MulEquiv_piUnits(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonalRingHom___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Function_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uMat___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_f_3_, lean_object* v_i_4_, lean_object* v_j_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_eq(v_i_4_, v_j_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; uint8_t v___x_8_; 
lean_inc(v_j_5_);
lean_inc(v_i_4_);
v___x_7_ = lean_apply_2(v_inst_2_, v_i_4_, v_j_5_);
v___x_8_ = lean_unbox(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v_toSemiring_9_; lean_object* v___x_10_; lean_object* v_toZero_11_; 
lean_dec(v_j_5_);
lean_dec(v_i_4_);
lean_dec(v_f_3_);
v_toSemiring_9_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_9_);
lean_dec_ref(v_inst_1_);
v___x_10_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_9_);
v_toZero_11_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_toZero_11_);
lean_dec_ref(v___x_10_);
return v_toZero_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v_inst_1_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_i_4_);
lean_ctor_set(v___x_12_, 1, v_j_5_);
v___x_13_ = lean_apply_1(v_f_3_, v___x_12_);
return v___x_13_;
}
}
else
{
lean_object* v___x_14_; lean_object* v_toAddMonoidWithOne_15_; lean_object* v_toOne_16_; 
lean_dec(v_j_5_);
lean_dec(v_i_4_);
lean_dec(v_f_3_);
lean_dec_ref(v_inst_2_);
v___x_14_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_15_ = lean_ctor_get(v___x_14_, 1);
lean_inc_ref(v_toAddMonoidWithOne_15_);
lean_dec_ref(v___x_14_);
v_toOne_16_ = lean_ctor_get(v_toAddMonoidWithOne_15_, 2);
lean_inc(v_toOne_16_);
lean_dec_ref(v_toAddMonoidWithOne_15_);
return v_toOne_16_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uMat(lean_object* v_n_17_, lean_object* v_00_u03ba_18_, lean_object* v_inst_19_, lean_object* v_P_20_, lean_object* v_inst_21_, lean_object* v_f_22_, lean_object* v_i_23_, lean_object* v_j_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_L2_Col_uMat___redArg(v_inst_19_, v_inst_21_, v_f_22_, v_i_23_, v_j_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uMat___boxed(lean_object* v_n_26_, lean_object* v_00_u03ba_27_, lean_object* v_inst_28_, lean_object* v_P_29_, lean_object* v_inst_30_, lean_object* v_f_31_, lean_object* v_i_32_, lean_object* v_j_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_L2_Col_uMat(v_n_26_, v_00_u03ba_27_, v_inst_28_, v_P_29_, v_inst_30_, v_f_31_, v_i_32_, v_j_33_);
lean_dec(v_n_26_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__0(lean_object* v_toMonoid_35_, lean_object* v_i_36_){
_start:
{
lean_inc_ref(v_toMonoid_35_);
return v_toMonoid_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__0___boxed(lean_object* v_toMonoid_37_, lean_object* v_i_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_L2_Col_dGL___redArg___lam__0(v_toMonoid_37_, v_i_38_);
lean_dec(v_i_38_);
lean_dec_ref(v_toMonoid_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__1(lean_object* v_toMonoid_40_, lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; lean_object* v_toOne_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
v___x_42_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_40_);
v_toOne_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v___x_42_, 1);
lean_dec(v_unused_51_);
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_toOne_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
lean_inc(v_toOne_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v_toOne_43_);
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_toOne_43_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_toOne_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg___lam__1___boxed(lean_object* v_toMonoid_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_L2_Col_dGL___redArg___lam__1(v_toMonoid_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec_ref(v_toMonoid_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL___redArg(lean_object* v_n_55_, lean_object* v_inst_56_, lean_object* v_i_u2080_57_, lean_object* v_u_58_){
_start:
{
lean_object* v_toSemiring_59_; lean_object* v_toMonoid_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_toFun_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_toSemiring_59_ = lean_ctor_get(v_inst_56_, 0);
lean_inc_ref(v_toSemiring_59_);
lean_dec_ref(v_inst_56_);
v_toMonoid_60_ = lean_ctor_get(v_toSemiring_59_, 1);
lean_inc_ref_n(v_toMonoid_60_, 2);
v___f_61_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_dGL___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_61_, 0, v_toMonoid_60_);
v___x_62_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_59_);
v___x_63_ = lp_mathlib_MulEquiv_piUnits(lean_box(0), lean_box(0), v___f_61_);
lean_dec_ref(v___f_61_);
v___x_64_ = lp_mathlib_Equiv_symm___redArg(v___x_63_);
v_toFun_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_toFun_65_);
lean_dec_ref(v___x_64_);
v___x_66_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_66_, 0, v_n_55_);
lean_inc_ref(v___x_66_);
v___x_67_ = lp_mathlib_Matrix_diagonalRingHom___redArg(v___x_62_, v___x_66_);
v___f_68_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_dGL___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_68_, 0, v_toMonoid_60_);
v___x_69_ = lean_alloc_closure((void*)(lp_mathlib_Function_update___boxed), 7, 6);
lean_closure_set(v___x_69_, 0, lean_box(0));
lean_closure_set(v___x_69_, 1, lean_box(0));
lean_closure_set(v___x_69_, 2, v___x_66_);
lean_closure_set(v___x_69_, 3, v___f_68_);
lean_closure_set(v___x_69_, 4, v_i_u2080_57_);
lean_closure_set(v___x_69_, 5, v_u_58_);
v___x_70_ = lean_apply_1(v_toFun_65_, v___x_69_);
v___x_71_ = lp_mathlib_Units_map___redArg___lam__0(v___x_67_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_dGL(lean_object* v_n_72_, lean_object* v_00_u03ba_73_, lean_object* v_inst_74_, lean_object* v_i_u2080_75_, lean_object* v_u_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_tree_Formalism_L2_Col_dGL___redArg(v_n_72_, v_inst_74_, v_i_u2080_75_, v_u_76_);
return v___x_77_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_LevGCount(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
