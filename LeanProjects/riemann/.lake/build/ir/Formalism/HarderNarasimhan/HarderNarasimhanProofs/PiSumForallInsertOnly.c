// Lean compiler output
// Module: Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly
// Imports: public import Init public meta import Init public import Formalism.HarderNarasimhan.DegSupermodZ public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe public import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
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
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Pi_module___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_completeLattice___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
lean_object* lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(lean_object*);
lean_object* lp_mathlib_Pi_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_WithLp_linearEquiv___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_single___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___redArg___lam__1(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HN_piSum__emb___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HN_piSum__emb___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_toAddCommGroup_4_; 
v___x_3_ = lean_apply_1(v_inst_1_, v_i_2_);
v_toAddCommGroup_4_ = lean_ctor_get(v___x_3_, 1);
lean_inc_ref(v_toAddCommGroup_4_);
lean_dec_ref(v___x_3_);
return v_toAddCommGroup_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___redArg___lam__1(lean_object* v_inst_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; lean_object* v_toAddCommGroup_8_; lean_object* v_toAddMonoid_9_; 
v___x_7_ = lean_apply_1(v_inst_5_, v_i_6_);
v_toAddCommGroup_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc_ref(v_toAddCommGroup_8_);
lean_dec_ref(v___x_7_);
v_toAddMonoid_9_ = lean_ctor_get(v_toAddCommGroup_8_, 0);
lean_inc_ref(v_toAddMonoid_9_);
lean_dec_ref(v_toAddCommGroup_8_);
return v_toAddMonoid_9_;
}
}
static lean_object* _init_lp_tree_Formalism_HN_piSum__emb___redArg___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(2u);
v___x_11_ = lp_mathlib_ENNReal_instAddCommMonoidWithOne___lam__0(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___redArg(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_i_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toLinearMap_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___f_23_; 
lean_inc_ref(v_inst_13_);
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_piSum__emb___redArg___lam__0), 2, 1);
lean_closure_set(v___f_15_, 0, v_inst_13_);
v___x_16_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_15_);
v___x_17_ = lean_obj_once(&lp_tree_Formalism_HN_piSum__emb___redArg___closed__0, &lp_tree_Formalism_HN_piSum__emb___redArg___closed__0_once, _init_lp_tree_Formalism_HN_piSum__emb___redArg___closed__0);
v___x_18_ = lp_mathlib_WithLp_linearEquiv___redArg(v___x_17_, v___x_16_);
lean_dec_ref(v___x_16_);
v___x_19_ = lp_mathlib_LinearEquiv_symm___redArg(v___x_18_);
v_toLinearMap_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_toLinearMap_20_);
lean_dec_ref(v___x_19_);
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_piSum__emb___redArg___lam__1), 2, 1);
lean_closure_set(v___f_21_, 0, v_inst_13_);
v___x_22_ = lp_mathlib_LinearMap_single___redArg(v___f_21_, v_inst_12_, v_i_14_);
v___f_23_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_23_, 0, v___x_22_);
lean_closure_set(v___f_23_, 1, v_toLinearMap_20_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb(lean_object* v_00_u03b9_24_, lean_object* v_inst_25_, lean_object* v_E_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_i_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_tree_Formalism_HN_piSum__emb___redArg(v_inst_25_, v_inst_27_, v_i_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSum__emb___boxed(lean_object* v_00_u03b9_31_, lean_object* v_inst_32_, lean_object* v_E_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_i_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_HN_piSum__emb(v_00_u03b9_31_, v_inst_32_, v_E_33_, v_inst_34_, v_inst_35_, v_i_36_);
lean_dec_ref(v_inst_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumS(lean_object* v_R_38_, lean_object* v_inst_39_, lean_object* v_00_u03b9_40_, lean_object* v_inst_41_, lean_object* v_V_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_L_45_, lean_object* v_i_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumS___boxed(lean_object* v_R_48_, lean_object* v_inst_49_, lean_object* v_00_u03b9_50_, lean_object* v_inst_51_, lean_object* v_V_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_L_55_, lean_object* v_i_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_Formalism_HN_piSumS(v_R_48_, v_inst_49_, v_00_u03b9_50_, v_inst_51_, v_V_52_, v_inst_53_, v_inst_54_, v_L_55_, v_i_56_);
lean_dec(v_i_56_);
lean_dec_ref(v_L_55_);
lean_dec(v_inst_54_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_49_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___redArg___lam__0(lean_object* v_inst_58_, lean_object* v_i_59_){
_start:
{
lean_object* v___x_60_; lean_object* v_toAddMonoid_61_; 
v___x_60_ = lean_apply_1(v_inst_58_, v_i_59_);
v_toAddMonoid_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_toAddMonoid_61_);
lean_dec_ref(v___x_60_);
return v_toAddMonoid_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v_toSemiring_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_toSupSet_71_; lean_object* v___x_72_; 
v_toSemiring_65_ = lean_ctor_get(v_inst_62_, 0);
v___f_66_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_piSumT___redArg___lam__0), 2, 1);
lean_closure_set(v___f_66_, 0, v_inst_63_);
v___x_67_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_66_);
v___x_68_ = lp_mathlib_Pi_module___redArg(v_inst_64_);
v___x_69_ = lp_mathlib_Submodule_completeLattice___redArg(v_toSemiring_65_, v___x_67_, v___x_68_);
lean_dec(v___x_68_);
lean_dec_ref(v___x_67_);
v___x_70_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_69_);
v_toSupSet_71_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_toSupSet_71_);
lean_dec_ref(v___x_70_);
v___x_72_ = lean_apply_1(v_toSupSet_71_, lean_box(0));
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___redArg___boxed(lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_HN_piSumT___redArg(v_inst_73_, v_inst_74_, v_inst_75_);
lean_dec_ref(v_inst_73_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT(lean_object* v_R_77_, lean_object* v_inst_78_, lean_object* v_00_u03b9_79_, lean_object* v_inst_80_, lean_object* v_V_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_L_84_, lean_object* v_s_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_tree_Formalism_HN_piSumT___redArg(v_inst_78_, v_inst_82_, v_inst_83_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_piSumT___boxed(lean_object* v_R_87_, lean_object* v_inst_88_, lean_object* v_00_u03b9_89_, lean_object* v_inst_90_, lean_object* v_V_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_L_94_, lean_object* v_s_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_Formalism_HN_piSumT(v_R_87_, v_inst_88_, v_00_u03b9_89_, v_inst_90_, v_V_91_, v_inst_92_, v_inst_93_, v_L_94_, v_s_95_);
lean_dec(v_s_95_);
lean_dec_ref(v_L_94_);
lean_dec_ref(v_inst_90_);
lean_dec_ref(v_inst_88_);
return v_res_96_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_DegSupermodZ(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_DegSupermodZ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
