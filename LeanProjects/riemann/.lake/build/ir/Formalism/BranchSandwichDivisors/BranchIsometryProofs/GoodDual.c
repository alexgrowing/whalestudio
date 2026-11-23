// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.BranchIsometryProofs.GoodDual
// Imports: public import Init public meta import Init public import Formalism.BranchSandwichDivisors.StatementL public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
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
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___redArg___lam__0(lean_object* v_g_1_, lean_object* v_inst_2_, lean_object* v_y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_g_1_, v_y_3_);
v___x_5_ = lean_apply_1(v_inst_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___redArg(lean_object* v_inst_6_, lean_object* v_g_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___redArg___lam__0), 3, 2);
lean_closure_set(v___f_8_, 0, v_g_7_);
lean_closure_set(v___f_8_, 1, v_inst_6_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw(lean_object* v_K_9_, lean_object* v_V_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_g_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_g_15_);
lean_closure_set(v___f_16_, 1, v_inst_12_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw___boxed(lean_object* v_K_17_, lean_object* v_V_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_g_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_BranchingDeterminantCap_GoodDualLattice_tw(v_K_17_, v_V_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_g_23_);
lean_dec(v_inst_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_19_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementL(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
