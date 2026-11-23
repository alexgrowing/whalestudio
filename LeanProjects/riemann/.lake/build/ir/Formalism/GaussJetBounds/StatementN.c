// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementN
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementI
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__0(lean_object* v_c_1_, lean_object* v_x_2_, lean_object* v_L_3_, lean_object* v_L_x27_4_, lean_object* v_toMul_5_, lean_object* v_toAdd_6_, lean_object* v_y_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
lean_inc_n(v_y_7_, 2);
lean_inc_n(v_x_2_, 2);
v___x_8_ = lean_apply_2(v_c_1_, v_x_2_, v_y_7_);
lean_inc(v_L_3_);
v___x_9_ = lean_apply_1(v_L_3_, v_x_2_);
lean_inc(v_L_x27_4_);
v___x_10_ = lean_apply_1(v_L_x27_4_, v_y_7_);
lean_inc_n(v_toMul_5_, 2);
v___x_11_ = lean_apply_2(v_toMul_5_, v___x_9_, v___x_10_);
v___x_12_ = lean_apply_1(v_L_3_, v_y_7_);
v___x_13_ = lean_apply_1(v_L_x27_4_, v_x_2_);
v___x_14_ = lean_apply_2(v_toMul_5_, v___x_12_, v___x_13_);
v___x_15_ = lean_apply_2(v_toAdd_6_, v___x_11_, v___x_14_);
v___x_16_ = lean_apply_2(v_toMul_5_, v___x_8_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__1(lean_object* v_c_17_, lean_object* v_L_18_, lean_object* v_L_x27_19_, lean_object* v_toMul_20_, lean_object* v_toAdd_21_, lean_object* v_toAddCommMonoid_22_, lean_object* v_inst_23_, lean_object* v_x_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__0), 7, 6);
lean_closure_set(v___f_25_, 0, v_c_17_);
lean_closure_set(v___f_25_, 1, v_x_24_);
lean_closure_set(v___f_25_, 2, v_L_18_);
lean_closure_set(v___f_25_, 3, v_L_x27_19_);
lean_closure_set(v___f_25_, 4, v_toMul_20_);
lean_closure_set(v___f_25_, 5, v_toAdd_21_);
v___x_26_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_22_, v_inst_23_, v___f_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__1___boxed(lean_object* v_c_27_, lean_object* v_L_28_, lean_object* v_L_x27_29_, lean_object* v_toMul_30_, lean_object* v_toAdd_31_, lean_object* v_toAddCommMonoid_32_, lean_object* v_inst_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__1(v_c_27_, v_L_28_, v_L_x27_29_, v_toMul_30_, v_toAdd_31_, v_toAddCommMonoid_32_, v_inst_33_, v_x_34_);
lean_dec_ref(v_toAddCommMonoid_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg(lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_c_38_, lean_object* v_L_39_, lean_object* v_L_x27_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_toSemiring_43_; lean_object* v_toAddCommMonoid_44_; lean_object* v___x_45_; lean_object* v_toMul_46_; lean_object* v_toAdd_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v___x_41_ = lp_mathlib_Field_toSemifield___redArg(v_inst_36_);
v___x_42_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_41_);
v_toSemiring_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc_ref(v_toSemiring_43_);
lean_dec_ref(v___x_42_);
v_toAddCommMonoid_44_ = lean_ctor_get(v_toSemiring_43_, 0);
lean_inc_ref_n(v_toAddCommMonoid_44_, 2);
v___x_45_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_43_);
v_toMul_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_toMul_46_);
v_toAdd_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_toAdd_47_);
lean_dec_ref(v___x_45_);
lean_inc(v_inst_37_);
v___f_48_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_48_, 0, v_c_38_);
lean_closure_set(v___f_48_, 1, v_L_39_);
lean_closure_set(v___f_48_, 2, v_L_x27_40_);
lean_closure_set(v___f_48_, 3, v_toMul_46_);
lean_closure_set(v___f_48_, 4, v_toAdd_47_);
lean_closure_set(v___f_48_, 5, v_toAddCommMonoid_44_);
lean_closure_set(v___f_48_, 6, v_inst_37_);
v___x_49_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_44_, v_inst_37_, v___f_48_);
lean_dec_ref(v_toAddCommMonoid_44_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg___boxed(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_c_52_, lean_object* v_L_53_, lean_object* v_L_x27_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg(v_inst_50_, v_inst_51_, v_c_52_, v_L_53_, v_L_x27_54_);
lean_dec_ref(v_inst_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar(lean_object* v_K_56_, lean_object* v_inst_57_, lean_object* v_00_u03b9_58_, lean_object* v_inst_59_, lean_object* v_c_60_, lean_object* v_L_61_, lean_object* v_L_x27_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_tree_Formalism_DworkPowerSeriesWeights_polar___redArg(v_inst_57_, v_inst_59_, v_c_60_, v_L_61_, v_L_x27_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_polar___boxed(lean_object* v_K_64_, lean_object* v_inst_65_, lean_object* v_00_u03b9_66_, lean_object* v_inst_67_, lean_object* v_c_68_, lean_object* v_L_69_, lean_object* v_L_x27_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_DworkPowerSeriesWeights_polar(v_K_64_, v_inst_65_, v_00_u03b9_66_, v_inst_67_, v_c_68_, v_L_69_, v_L_x27_70_);
lean_dec_ref(v_inst_65_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
