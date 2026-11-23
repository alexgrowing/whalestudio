// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementC public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds
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
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__F(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__F___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg___lam__0(lean_object* v_y_1_, lean_object* v_E_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc(v_b_4_);
v___x_5_ = lean_apply_1(v_y_1_, v_b_4_);
v___x_6_ = lean_apply_3(v_E_2_, v_a_3_, v_b_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg___lam__1(lean_object* v_E_7_, lean_object* v_n_8_, lean_object* v_toAddMonoid_9_, lean_object* v_y_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_12_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_CharId__M___redArg___lam__0), 4, 3);
lean_closure_set(v___f_12_, 0, v_y_10_);
lean_closure_set(v___f_12_, 1, v_E_7_);
lean_closure_set(v___f_12_, 2, v_a_11_);
v___x_13_ = l_List_finRange(v_n_8_);
v___x_14_ = lp_mathlib_Finset_sum___redArg(v_toAddMonoid_9_, v___x_13_, v___f_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg___lam__1___boxed(lean_object* v_E_15_, lean_object* v_n_16_, lean_object* v_toAddMonoid_17_, lean_object* v_y_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_REAL_CharId__M___redArg___lam__1(v_E_15_, v_n_16_, v_toAddMonoid_17_, v_y_18_, v_a_19_);
lean_dec_ref(v_toAddMonoid_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___redArg(lean_object* v_inst_21_, lean_object* v_n_22_, lean_object* v_E_23_){
_start:
{
lean_object* v_toAddMonoid_24_; lean_object* v___f_25_; 
v_toAddMonoid_24_ = lean_ctor_get(v_inst_21_, 0);
lean_inc_ref(v_toAddMonoid_24_);
lean_dec_ref(v_inst_21_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_CharId__M___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_25_, 0, v_E_23_);
lean_closure_set(v___f_25_, 1, v_n_22_);
lean_closure_set(v___f_25_, 2, v_toAddMonoid_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M(lean_object* v_V_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_E_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_Formalism_REAL_CharId__M___redArg(v_inst_27_, v_n_29_, v_E_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__M___boxed(lean_object* v_V_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_n_35_, lean_object* v_E_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_REAL_CharId__M(v_V_32_, v_inst_33_, v_inst_34_, v_n_35_, v_E_36_);
lean_dec(v_inst_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___redArg___lam__0(lean_object* v_E_38_, lean_object* v_c_39_, lean_object* v_d_40_, lean_object* v_inst_41_, lean_object* v_toSub_42_, lean_object* v_y_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_inc(v_y_43_);
lean_inc(v_x_44_);
v___x_45_ = lean_apply_1(v_y_43_, v_x_44_);
lean_inc(v_d_40_);
lean_inc(v_c_39_);
v___x_46_ = lean_apply_3(v_E_38_, v_c_39_, v_d_40_, v___x_45_);
v___x_47_ = lean_nat_dec_eq(v_x_44_, v_d_40_);
lean_dec(v_d_40_);
lean_dec(v_x_44_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v_toZero_49_; lean_object* v___x_50_; 
lean_dec(v_y_43_);
lean_dec(v_c_39_);
v___x_48_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_inst_41_);
v_toZero_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_toZero_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_apply_2(v_toSub_42_, v___x_46_, v_toZero_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_apply_1(v_y_43_, v_c_39_);
v___x_52_ = lean_apply_2(v_toSub_42_, v___x_46_, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___redArg___lam__0___boxed(lean_object* v_E_53_, lean_object* v_c_54_, lean_object* v_d_55_, lean_object* v_inst_56_, lean_object* v_toSub_57_, lean_object* v_y_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_REAL_twistedAction___redArg___lam__0(v_E_53_, v_c_54_, v_d_55_, v_inst_56_, v_toSub_57_, v_y_58_, v_x_59_);
lean_dec_ref(v_inst_56_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___redArg(lean_object* v_inst_61_, lean_object* v_E_62_, lean_object* v_c_63_, lean_object* v_d_64_){
_start:
{
lean_object* v_toSub_65_; lean_object* v___f_66_; 
v_toSub_65_ = lean_ctor_get(v_inst_61_, 2);
lean_inc(v_toSub_65_);
v___f_66_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_twistedAction___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_66_, 0, v_E_62_);
lean_closure_set(v___f_66_, 1, v_c_63_);
lean_closure_set(v___f_66_, 2, v_d_64_);
lean_closure_set(v___f_66_, 3, v_inst_61_);
lean_closure_set(v___f_66_, 4, v_toSub_65_);
return v___f_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction(lean_object* v_V_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_E_71_, lean_object* v_c_72_, lean_object* v_d_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_REAL_twistedAction___redArg(v_inst_68_, v_E_71_, v_c_72_, v_d_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_twistedAction___boxed(lean_object* v_V_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_n_78_, lean_object* v_E_79_, lean_object* v_c_80_, lean_object* v_d_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_tree_Formalism_REAL_twistedAction(v_V_75_, v_inst_76_, v_inst_77_, v_n_78_, v_E_79_, v_c_80_, v_d_81_);
lean_dec(v_n_78_);
lean_dec(v_inst_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__F(lean_object* v_V_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_n_86_, lean_object* v_E_87_, lean_object* v_v_88_, lean_object* v_j_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_CharId__F___boxed(lean_object* v_V_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_n_94_, lean_object* v_E_95_, lean_object* v_v_96_, lean_object* v_j_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_REAL_CharId__F(v_V_91_, v_inst_92_, v_inst_93_, v_n_94_, v_E_95_, v_v_96_, v_j_97_);
lean_dec(v_j_97_);
lean_dec(v_v_96_);
lean_dec(v_E_95_);
lean_dec(v_n_94_);
lean_dec(v_inst_93_);
lean_dec_ref(v_inst_92_);
return v_res_98_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementC(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
