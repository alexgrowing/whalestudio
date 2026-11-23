// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataSpaces
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.HermitianLattices.StatementLat public import Formalism.HermitianLattices.StatementMass public import Formalism.SatakeDualWeyl.Statement
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
lean_object* lp_tree_Formalism_BasicNotions_Ranks_rankY(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HSpace_hD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HSpace_hD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HSpace_hD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sigYD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sigYD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig___redArg(lean_object* v_inst_1_){
_start:
{
lean_inc(v_inst_1_);
return v_inst_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig___redArg___boxed(lean_object* v_inst_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_BasicNotions_CMData_sig___redArg(v_inst_2_);
lean_dec(v_inst_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig(lean_object* v_F_4_, lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_hc_12_){
_start:
{
lean_inc(v_inst_10_);
return v_inst_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_CMData_sig___boxed(lean_object* v_F_13_, lean_object* v_E_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_hc_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_BasicNotions_CMData_sig(v_F_13_, v_E_14_, v_inst_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_hc_21_);
lean_dec_ref(v_inst_20_);
lean_dec(v_inst_19_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_15_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HSpace_hD___redArg(lean_object* v_S_23_, lean_object* v_x_24_, lean_object* v_y_25_){
_start:
{
lean_object* v_hT_26_; lean_object* v___x_27_; 
v_hT_26_ = lean_ctor_get(v_S_23_, 3);
lean_inc(v_hT_26_);
lean_dec_ref(v_S_23_);
v___x_27_ = lean_apply_2(v_hT_26_, v_y_25_, v_x_24_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HSpace_hD(lean_object* v_E_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_S_32_, lean_object* v_x_33_, lean_object* v_y_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_tree_Formalism_BasicNotions_HSpace_hD___redArg(v_S_32_, v_x_33_, v_y_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HSpace_hD___boxed(lean_object* v_E_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_S_40_, lean_object* v_x_41_, lean_object* v_y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_BasicNotions_HSpace_hD(v_E_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_S_40_, v_x_41_, v_y_42_);
lean_dec(v_inst_39_);
lean_dec_ref(v_inst_37_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sigYD(lean_object* v_R_44_, lean_object* v_j_45_){
_start:
{
lean_object* v_m_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_m_46_ = lean_ctor_get(v_R_44_, 2);
v___x_47_ = lp_tree_Formalism_BasicNotions_Ranks_rankY(v_R_44_, v_j_45_);
v___x_48_ = lean_nat_sub(v_m_46_, v_j_45_);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_shiftr(v___x_48_, v___x_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_nat_sub(v___x_47_, v___x_50_);
lean_dec(v___x_47_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_sigYD___boxed(lean_object* v_R_53_, lean_object* v_j_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_BasicNotions_sigYD(v_R_53_, v_j_54_);
lean_dec(v_j_54_);
lean_dec_ref(v_R_53_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementMass(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataSpaces(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementMass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
