// Lean compiler output
// Module: Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.DataDIV public import Formalism.DegreeFormula.FlagDegFormula public import Formalism.DegreeFormula.Statement public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_jcl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_jcl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N___redArg(lean_object* v_w_1_){
_start:
{
lean_object* v_S_2_; lean_object* v_rank_3_; 
v_S_2_ = lean_ctor_get(v_w_1_, 0);
v_rank_3_ = lean_ctor_get(v_S_2_, 4);
lean_inc(v_rank_3_);
return v_rank_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N___redArg___boxed(lean_object* v_w_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_L2_Geo_Dat_N___redArg(v_w_4_);
lean_dec_ref(v_w_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N(lean_object* v_D_6_, lean_object* v_Lev_7_, lean_object* v_w_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lp_tree_Formalism_L2_Geo_Dat_N___redArg(v_w_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_Dat_N___boxed(lean_object* v_D_10_, lean_object* v_Lev_11_, lean_object* v_w_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_L2_Geo_Dat_N(v_D_10_, v_Lev_11_, v_w_12_);
lean_dec_ref(v_w_12_);
lean_dec_ref(v_D_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_jcl(lean_object* v_D_14_, lean_object* v_j_15_){
_start:
{
lean_object* v_R_16_; lean_object* v_m_17_; lean_object* v___x_18_; lean_object* v___y_20_; uint8_t v___x_22_; 
v_R_16_ = lean_ctor_get(v_D_14_, 0);
v_m_17_ = lean_ctor_get(v_R_16_, 2);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_dec_le(v_j_15_, v_m_17_);
if (v___x_22_ == 0)
{
v___y_20_ = v_m_17_;
goto v___jp_19_;
}
else
{
v___y_20_ = v_j_15_;
goto v___jp_19_;
}
v___jp_19_:
{
uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_le(v___x_18_, v___y_20_);
if (v___x_21_ == 0)
{
return v___x_18_;
}
else
{
lean_inc(v___y_20_);
return v___y_20_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_jcl___boxed(lean_object* v_D_23_, lean_object* v_j_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_L2_Geo_jcl(v_D_23_, v_j_24_);
lean_dec(v_j_24_);
lean_dec_ref(v_D_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW___redArg(lean_object* v_D_26_, lean_object* v_00_u03ba_27_, lean_object* v_j_28_){
_start:
{
lean_object* v_sp_29_; lean_object* v_R_30_; lean_object* v_W_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_fst_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_sp_29_ = lean_ctor_get(v_D_26_, 2);
v_R_30_ = lean_ctor_get(v_D_26_, 0);
lean_inc_ref(v_R_30_);
v_W_31_ = lean_ctor_get(v_sp_29_, 11);
lean_inc_ref(v_W_31_);
v___x_32_ = lp_tree_Formalism_L2_Geo_jcl(v_D_26_, v_j_28_);
lean_dec_ref(v_D_26_);
v___x_33_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_30_, v___x_32_);
lean_dec_ref(v_R_30_);
v_fst_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_fst_34_);
lean_dec_ref(v___x_33_);
v___x_35_ = lean_apply_1(v_W_31_, v___x_32_);
v___x_36_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v_00_u03ba_27_);
lean_ctor_set(v___x_36_, 2, v_fst_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW___redArg___boxed(lean_object* v_D_37_, lean_object* v_00_u03ba_38_, lean_object* v_j_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Geo_datW___redArg(v_D_37_, v_00_u03ba_38_, v_j_39_);
lean_dec(v_j_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW(lean_object* v_D_41_, lean_object* v_Lev_42_, lean_object* v_00_u03ba_43_, lean_object* v_j_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_tree_Formalism_L2_Geo_datW___redArg(v_D_41_, v_00_u03ba_43_, v_j_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_datW___boxed(lean_object* v_D_46_, lean_object* v_Lev_47_, lean_object* v_00_u03ba_48_, lean_object* v_j_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_L2_Geo_datW(v_D_46_, v_Lev_47_, v_00_u03ba_48_, v_j_49_);
lean_dec(v_j_49_);
return v_res_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_DegreeFormula_FlagDegFormula(uint8_t builtin);
lean_object* initialize_tree_Formalism_DegreeFormula_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_DegFlLApply(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DegreeFormula_FlagDegFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DegreeFormula_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
