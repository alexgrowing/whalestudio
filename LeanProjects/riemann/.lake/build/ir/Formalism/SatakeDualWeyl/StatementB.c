// Lean compiler output
// Module: Formalism.SatakeDualWeyl.StatementB
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.Statement public import Formalism.HermitianLattices.StatementLat
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
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Pi_single___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_toLin___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_GeneralLinearGroup_generalLinearEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___redArg___lam__0(lean_object* v_toZero_1_, lean_object* v_i_2_){
_start:
{
lean_inc(v_toZero_1_);
return v_toZero_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___redArg___lam__0___boxed(lean_object* v_toZero_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_UG_gram___redArg___lam__0(v_toZero_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec(v_toZero_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___redArg(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_h_8_, lean_object* v_i_9_, lean_object* v_j_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toSemiring_13_; lean_object* v___x_14_; lean_object* v_toZero_15_; lean_object* v___x_16_; lean_object* v_toRing_17_; lean_object* v___x_18_; lean_object* v_toAddMonoidWithOne_19_; lean_object* v_toOne_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_11_ = lp_mathlib_Field_toSemifield___redArg(v_inst_6_);
v___x_12_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_11_);
v_toSemiring_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc_ref(v_toSemiring_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_13_);
v_toZero_15_ = lean_ctor_get(v___x_14_, 1);
lean_inc(v_toZero_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_6_);
v_toRing_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_toRing_17_);
lean_dec_ref(v___x_16_);
v___x_18_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_17_);
v_toAddMonoidWithOne_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc_ref(v_toAddMonoidWithOne_19_);
lean_dec_ref(v___x_18_);
v_toOne_20_ = lean_ctor_get(v_toAddMonoidWithOne_19_, 2);
lean_inc_n(v_toOne_20_, 2);
lean_dec_ref(v_toAddMonoidWithOne_19_);
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_gram___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_21_, 0, v_toZero_15_);
lean_inc_ref(v_inst_7_);
lean_inc_ref(v___f_21_);
v___x_22_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_22_, 0, lean_box(0));
lean_closure_set(v___x_22_, 1, lean_box(0));
lean_closure_set(v___x_22_, 2, v___f_21_);
lean_closure_set(v___x_22_, 3, v_inst_7_);
lean_closure_set(v___x_22_, 4, v_i_9_);
lean_closure_set(v___x_22_, 5, v_toOne_20_);
v___x_23_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_23_, 0, lean_box(0));
lean_closure_set(v___x_23_, 1, lean_box(0));
lean_closure_set(v___x_23_, 2, v___f_21_);
lean_closure_set(v___x_23_, 3, v_inst_7_);
lean_closure_set(v___x_23_, 4, v_j_10_);
lean_closure_set(v___x_23_, 5, v_toOne_20_);
v___x_24_ = lean_apply_2(v_h_8_, v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram(lean_object* v_K_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_n_28_, lean_object* v_inst_29_, lean_object* v_h_30_, lean_object* v_i_31_, lean_object* v_j_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_UG_gram___redArg(v_inst_26_, v_inst_29_, v_h_30_, v_i_31_, v_j_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_gram___boxed(lean_object* v_K_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_n_37_, lean_object* v_inst_38_, lean_object* v_h_39_, lean_object* v_i_40_, lean_object* v_j_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_UG_gram(v_K_34_, v_inst_35_, v_inst_36_, v_n_37_, v_inst_38_, v_h_39_, v_i_40_, v_j_41_);
lean_dec(v_inst_36_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv___redArg___lam__0(lean_object* v_toAddCommMonoid_43_, lean_object* v_i_44_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_43_);
return v_toAddCommMonoid_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_45_, lean_object* v_i_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_UG_glEquiv___redArg___lam__0(v_toAddCommMonoid_45_, v_i_46_);
lean_dec(v_i_46_);
lean_dec_ref(v_toAddCommMonoid_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv___redArg(lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_g_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_toSemiring_54_; lean_object* v_toAddCommMonoid_55_; lean_object* v_toCommRing_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_toFun_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_toFun_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_52_ = lp_mathlib_Field_toSemifield___redArg(v_inst_48_);
v___x_53_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_52_);
v_toSemiring_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref(v_toSemiring_54_);
lean_dec_ref(v___x_53_);
v_toAddCommMonoid_55_ = lean_ctor_get(v_toSemiring_54_, 0);
v_toCommRing_56_ = lean_ctor_get(v_inst_48_, 0);
lean_inc_ref(v_toCommRing_56_);
lean_dec_ref(v_inst_48_);
lean_inc_ref(v_toAddCommMonoid_55_);
v___f_57_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_glEquiv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_57_, 0, v_toAddCommMonoid_55_);
v___x_58_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_57_);
v___x_59_ = lp_mathlib_Matrix_GeneralLinearGroup_toLin___redArg(v_inst_50_, v_inst_49_, v_toCommRing_56_);
v_toFun_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_toFun_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_54_);
v___x_62_ = lp_mathlib_Pi_Function_module___redArg(v___x_61_);
v___x_63_ = lp_mathlib_LinearMap_GeneralLinearGroup_generalLinearEquiv___redArg(v_toSemiring_54_, v___x_58_, v___x_62_);
v_toFun_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_toFun_64_);
lean_dec_ref(v___x_63_);
v___x_65_ = lean_apply_1(v_toFun_60_, v_g_51_);
v___x_66_ = lean_apply_1(v_toFun_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_glEquiv(lean_object* v_K_67_, lean_object* v_inst_68_, lean_object* v_n_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_g_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_tree_Formalism_UG_glEquiv___redArg(v_inst_68_, v_inst_70_, v_inst_71_, v_g_72_);
return v___x_73_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
