// Lean compiler output
// Module: Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.GaloisToProductIsIso public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
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
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_quadraticChar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MulChar_toUnitHom___redArg(lean_object*);
extern lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sgn2;
static lean_once_cell_t lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sQ(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg(lean_object* v_l_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_toFun_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_63__overap_10_; lean_object* v___x_11_; lean_object* v___x_66__overap_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_4_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg___closed__0, &lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg___closed__0_once, _init_lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg___closed__0);
lean_inc(v_l_2_);
v___x_5_ = lp_mathlib_ZMod_instField___redArg(v_l_2_);
v_toFun_6_ = lean_ctor_get(v___x_4_, 0);
v___x_7_ = lp_mathlib_ZMod_fintype___redArg(v_l_2_);
v___x_8_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_8_, 0, v_l_2_);
v___x_9_ = lp_mathlib_quadraticChar___redArg(v___x_5_, v___x_7_, v___x_8_);
lean_dec_ref(v___x_5_);
v___x_63__overap_10_ = lp_mathlib_MulChar_toUnitHom___redArg(v___x_9_);
v___x_11_ = lean_apply_1(v___x_63__overap_10_, v_x_3_);
v___x_66__overap_12_ = lp_tree_Formalism_LFunctionChainParameters_LHost_sgn2;
v___x_13_ = lean_apply_1(v___x_66__overap_12_, v___x_11_);
lean_inc(v_toFun_6_);
v___x_14_ = lean_apply_1(v_toFun_6_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sQ(lean_object* v_l_15_, lean_object* v_inst_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_LFunctionChainParameters_LHost_sQ___redArg(v_l_15_, v_x_17_);
return v___x_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_GaloisToProductIsIso(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_GaloisToProductIsIso(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
