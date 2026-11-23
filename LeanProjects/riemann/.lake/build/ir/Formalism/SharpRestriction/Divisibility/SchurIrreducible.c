// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.SchurIrreducible
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SatakeDualWeyl.Statement public import Formalism.LocalRingCardinality.DataTheta
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
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_TensorAlgebra_definition___lam__0_00___x40_Mathlib_LinearAlgebra_TensorAlgebra_Basic_2393025000____hygCtx___hyg_8_(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instCommSemiring;
lean_object* lp_mathlib_Algebra_id___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_instRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LieRing_ofAssociativeRing___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_instAlgebra___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instRingUniversalEnvelopingAlgebra___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instAlgebraUniversalEnvelopingAlgebra___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_addCommGroup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_leftHasSMul___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_Quotient_addMonoid___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_Quotient_instSMul_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_completeLattice___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_LinearMap_rTensorHom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_lTensor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_kroneckerMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__0(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__0_value;
static const lean_closure_object lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__1 = (const lean_object*)&lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_TensorAlgebra_definition___lam__0_00___x40_Mathlib_LinearAlgebra_TensorAlgebra_Basic_2393025000____hygCtx___hyg_8_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___closed__0 = (const lean_object*)&lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ringConGen___at___00UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ringConGen___at___00UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0 = (const lean_object*)&lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0_value)} };
static const lean_object* lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__0 = (const lean_object*)&lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__0_value;
static const lean_closure_object lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_comp___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___closed__0_value),((lean_object*)&lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__0_value)} };
static const lean_object* lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__1 = (const lean_object*)&lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ug_u03b9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ug_u03b9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_SchurIrreducible_UgF_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_SchurIrreducible_UgF_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___boxed(lean_object**);
static lean_object* _init_lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0(lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___boxed(lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0(v___y_6_, v___y_7_);
lean_dec(v___y_7_);
lean_dec(v___y_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__1(lean_object* v_B_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg(v_B_9_, v___y_10_, v___y_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg(lean_object* v_B_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___f_18_; lean_object* v___x_19_; 
v___f_17_ = ((lean_object*)(lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___closed__0));
lean_inc_ref(v_B_14_);
v___f_18_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__1), 3, 1);
lean_closure_set(v___f_18_, 0, v_B_14_);
v___x_19_ = lp_mathlib_Matrix_fromBlocks___redArg(v___f_17_, v_B_14_, v___f_18_, v___f_17_, v_a_15_, v_a_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf(lean_object* v_p_20_, lean_object* v_q_21_, lean_object* v_B_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg(v_B_22_, v_a_23_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___boxed(lean_object* v_p_26_, lean_object* v_q_27_, lean_object* v_B_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_MainNotions_SchurIrreducible_pOf(v_p_26_, v_q_27_, v_B_28_, v_a_29_, v_a_30_);
lean_dec(v_q_27_);
lean_dec(v_p_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___lam__0(lean_object* v_p_32_, lean_object* v_q_33_, lean_object* v_d_34_, lean_object* v_i_35_, lean_object* v_j_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_37_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_37_, 0, v_p_32_);
v___x_38_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_38_, 0, v_q_33_);
lean_inc_ref(v_i_35_);
v___x_39_ = l_instDecidableEqSum_decEq___redArg(v___x_37_, v___x_38_, v_i_35_, v_j_36_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_dec_ref(v_i_35_);
lean_dec_ref(v_d_34_);
v___x_40_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
v___x_41_ = lean_apply_1(v_d_34_, v_i_35_);
return v___x_41_;
}
}
}
static lean_object* _init_lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___closed__0(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0(lean_object* v_p_43_, lean_object* v_q_44_, lean_object* v_d_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_48_; lean_object* v_toFun_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
v___x_48_ = lean_obj_once(&lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___closed__0, &lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___closed__0_once, _init_lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___closed__0);
v_toFun_49_ = lean_ctor_get(v___x_48_, 0);
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0___lam__0), 5, 3);
lean_closure_set(v___f_50_, 0, v_p_43_);
lean_closure_set(v___f_50_, 1, v_q_44_);
lean_closure_set(v___f_50_, 2, v_d_45_);
lean_inc(v_toFun_49_);
v___x_51_ = lean_apply_3(v_toFun_49_, v___f_50_, v_a_46_, v_a_47_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__0(lean_object* v_x1_52_, lean_object* v_x2_53_){
_start:
{
lean_object* v_re_54_; lean_object* v_im_55_; lean_object* v___x_56_; 
v_re_54_ = lean_ctor_get(v_x1_52_, 0);
lean_inc(v_re_54_);
v_im_55_ = lean_ctor_get(v_x1_52_, 1);
lean_inc(v_im_55_);
lean_dec_ref(v_x1_52_);
v___x_56_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_54_, v_im_55_, v_x2_53_);
return v___x_56_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___closed__0(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_58_ = lp_mathlib_Complex_ofReal(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1(lean_object* v_x_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__1(v_x_61_);
lean_dec_ref(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__2(lean_object* v_p_63_, lean_object* v_q_64_, lean_object* v___f_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_SchurIrreducible_adMat_spec__0(v_p_63_, v_q_64_, v___f_65_, v___y_66_, v___y_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_adMat(lean_object* v_p_71_, lean_object* v_q_72_, lean_object* v_Y_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_re_81_; lean_object* v_im_82_; lean_object* v___x_83_; lean_object* v_re_84_; lean_object* v_im_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_96_; 
v___f_76_ = ((lean_object*)(lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__0));
v___f_77_ = ((lean_object*)(lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___closed__1));
v___f_78_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SchurIrreducible_adMat___lam__2), 5, 3);
lean_closure_set(v___f_78_, 0, v_p_71_);
lean_closure_set(v___f_78_, 1, v_q_72_);
lean_closure_set(v___f_78_, 2, v___f_77_);
lean_inc_ref(v_Y_73_);
v___x_79_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_79_, 0, lean_box(0));
lean_closure_set(v___x_79_, 1, lean_box(0));
lean_closure_set(v___x_79_, 2, lean_box(0));
lean_closure_set(v___x_79_, 3, v_Y_73_);
lean_inc_ref(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc_ref(v___f_78_);
v___x_80_ = lp_mathlib_Matrix_kroneckerMap___redArg(v___f_76_, v_Y_73_, v___f_78_, v_a_74_, v_a_75_);
v_re_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_re_81_);
v_im_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_im_82_);
lean_dec(v___x_80_);
v___x_83_ = lp_mathlib_Matrix_kroneckerMap___redArg(v___f_76_, v___f_78_, v___x_79_, v_a_74_, v_a_75_);
v_re_84_ = lean_ctor_get(v___x_83_, 0);
v_im_85_ = lean_ctor_get(v___x_83_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_96_ == 0)
{
v___x_87_ = v___x_83_;
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_im_85_);
lean_inc(v_re_84_);
lean_dec(v___x_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_94_; 
v___f_89_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_89_, 0, v_re_84_);
v___f_90_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_90_, 0, v_re_81_);
lean_closure_set(v___f_90_, 1, v___f_89_);
v___f_91_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_91_, 0, v_im_85_);
v___f_92_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_92_, 0, v_im_82_);
lean_closure_set(v___f_92_, 1, v___f_91_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v___f_92_);
lean_ctor_set(v___x_87_, 0, v___f_90_);
v___x_94_ = v___x_87_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___f_90_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___f_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___lam__0(lean_object* v_h_97_, lean_object* v_i_98_, lean_object* v_j_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_eq(v_i_98_, v_j_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec(v_i_98_);
lean_dec(v_h_97_);
v___x_101_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg___lam__0___closed__0);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_apply_1(v_h_97_, v_i_98_);
v___x_103_ = lp_mathlib_Complex_ofReal(v___x_102_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___lam__0___boxed(lean_object* v_h_104_, lean_object* v_i_105_, lean_object* v_j_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___lam__0(v_h_104_, v_i_105_, v_j_106_);
lean_dec(v_j_106_);
return v_res_107_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg(lean_object* v_h_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; lean_object* v_toFun_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___closed__0);
v_toFun_113_ = lean_ctor_get(v___x_112_, 0);
v___f_114_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_114_, 0, v_h_109_);
lean_inc(v_toFun_113_);
v___x_115_ = lean_apply_1(v_toFun_113_, v___f_114_);
v___x_116_ = lp_tree_Formalism_MainNotions_SchurIrreducible_pOf___redArg(v___x_115_, v_a_110_, v_a_111_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf(lean_object* v_p_117_, lean_object* v_q_118_, lean_object* v_h_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___redArg(v_h_119_, v_a_120_, v_a_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_aOf___boxed(lean_object* v_p_123_, lean_object* v_q_124_, lean_object* v_h_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_tree_Formalism_MainNotions_SchurIrreducible_aOf(v_p_123_, v_q_124_, v_h_125_, v_a_126_, v_a_127_);
lean_dec(v_q_124_);
lean_dec(v_p_123_);
return v_res_128_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0(lean_object* v_a_u2081_130_, lean_object* v___f_131_, lean_object* v_a_u2082_132_, lean_object* v___x_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_136_; lean_object* v_toFun_137_; lean_object* v___x_242__overap_138_; lean_object* v___x_139_; lean_object* v___x_243__overap_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_136_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0___closed__0);
v_toFun_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v___y_134_);
v___x_242__overap_138_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v_a_u2081_130_, v___f_131_, v___y_134_);
lean_inc(v___y_135_);
v___x_139_ = lean_apply_1(v___x_242__overap_138_, v___y_135_);
v___x_243__overap_140_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v_a_u2082_132_, v___x_133_, v___y_134_);
v___x_141_ = lean_apply_1(v___x_243__overap_140_, v___y_135_);
lean_inc_n(v_toFun_137_, 3);
v___x_142_ = lean_apply_1(v_toFun_137_, v___x_139_);
v___x_143_ = lean_apply_1(v_toFun_137_, v___x_141_);
v___x_144_ = l_List_appendTR___redArg(v___x_142_, v___x_143_);
v___x_145_ = lean_apply_1(v_toFun_137_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_a_u2081_150_, lean_object* v_a_u2082_151_){
_start:
{
lean_object* v___x_152_; lean_object* v_toAddMonoid_153_; lean_object* v_toAddMonoid_154_; lean_object* v___f_155_; lean_object* v___x_156_; lean_object* v___f_157_; 
v___x_152_ = lp_mathlib_Complex_instCommSemiring;
v_toAddMonoid_153_ = lean_ctor_get(v_inst_146_, 0);
lean_inc_ref_n(v_toAddMonoid_153_, 2);
lean_dec_ref(v_inst_146_);
v_toAddMonoid_154_ = lean_ctor_get(v_inst_148_, 0);
lean_inc_ref_n(v_toAddMonoid_154_, 3);
lean_dec_ref(v_inst_148_);
lean_inc(v_inst_147_);
lean_inc_n(v_inst_149_, 2);
v___f_155_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_rTensorHom___redArg___lam__0), 7, 5);
lean_closure_set(v___f_155_, 0, v___x_152_);
lean_closure_set(v___f_155_, 1, v_toAddMonoid_154_);
lean_closure_set(v___f_155_, 2, v_toAddMonoid_153_);
lean_closure_set(v___f_155_, 3, v_inst_149_);
lean_closure_set(v___f_155_, 4, v_inst_147_);
v___x_156_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_lTensor), 12, 11);
lean_closure_set(v___x_156_, 0, lean_box(0));
lean_closure_set(v___x_156_, 1, v___x_152_);
lean_closure_set(v___x_156_, 2, lean_box(0));
lean_closure_set(v___x_156_, 3, lean_box(0));
lean_closure_set(v___x_156_, 4, lean_box(0));
lean_closure_set(v___x_156_, 5, v_toAddMonoid_153_);
lean_closure_set(v___x_156_, 6, v_toAddMonoid_154_);
lean_closure_set(v___x_156_, 7, v_toAddMonoid_154_);
lean_closure_set(v___x_156_, 8, v_inst_147_);
lean_closure_set(v___x_156_, 9, v_inst_149_);
lean_closure_set(v___x_156_, 10, v_inst_149_);
v___f_157_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg___lam__0), 6, 4);
lean_closure_set(v___f_157_, 0, v_a_u2081_150_);
lean_closure_set(v___f_157_, 1, v___f_155_);
lean_closure_set(v___f_157_, 2, v_a_u2082_151_);
lean_closure_set(v___f_157_, 3, v___x_156_);
return v___f_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct(lean_object* v_p_158_, lean_object* v_q_159_, lean_object* v_V_u2081_160_, lean_object* v_V_u2082_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_a_u2081_166_, lean_object* v_a_u2082_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___redArg(v_inst_162_, v_inst_163_, v_inst_164_, v_inst_165_, v_a_u2081_166_, v_a_u2082_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct___boxed(lean_object* v_p_169_, lean_object* v_q_170_, lean_object* v_V_u2081_171_, lean_object* v_V_u2082_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_a_u2081_177_, lean_object* v_a_u2082_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lp_tree_Formalism_MainNotions_SchurIrreducible_tensAct(v_p_169_, v_q_170_, v_V_u2081_171_, v_V_u2082_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_inst_176_, v_a_u2081_177_, v_a_u2082_178_);
lean_dec(v_q_170_);
lean_dec(v_p_169_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2(lean_object* v_p_181_, lean_object* v_q_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = ((lean_object*)(lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___closed__0));
return v___f_183_;
}
}
LEAN_EXPORT lean_object* lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2___boxed(lean_object* v_p_184_, lean_object* v_q_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = lp_tree_TensorAlgebra_00_u03b9___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__2(v_p_184_, v_q_185_);
lean_dec(v_q_185_);
lean_dec(v_p_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg___lam__0(lean_object* v_00_u03c6_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_apply_1(v_00_u03c6_187_, v___y_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg(lean_object* v_00_u03c6_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(v___f_191_, 0, v_00_u03c6_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* lp_tree_ringConGen___at___00UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1_spec__4(lean_object* v_p_192_, lean_object* v_q_193_, lean_object* v_r_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* lp_tree_ringConGen___at___00UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_p_196_, lean_object* v_q_197_, lean_object* v_r_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = lp_tree_ringConGen___at___00UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1_spec__4(v_p_196_, v_q_197_, v_r_198_);
lean_dec(v_q_197_);
lean_dec(v_p_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___lam__0(lean_object* v___y_200_){
_start:
{
lean_inc(v___y_200_);
return v___y_200_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___lam__0(v___y_201_);
lean_dec(v___y_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6(lean_object* v_p_204_, lean_object* v_q_205_, lean_object* v_c_206_){
_start:
{
lean_object* v___f_207_; 
v___f_207_ = ((lean_object*)(lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0));
return v___f_207_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_p_208_, lean_object* v_q_209_, lean_object* v_c_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6(v_p_208_, v_q_209_, v_c_210_);
lean_dec(v_q_209_);
lean_dec(v_p_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2(lean_object* v_p_212_, lean_object* v_q_213_, lean_object* v_c_214_){
_start:
{
lean_object* v___f_215_; 
v___f_215_ = ((lean_object*)(lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0));
return v___f_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2___boxed(lean_object* v_p_216_, lean_object* v_q_217_, lean_object* v_c_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = lp_tree_RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2(v_p_216_, v_q_217_, v_c_218_);
lean_dec(v_q_217_);
lean_dec(v_p_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0(lean_object* v_p_220_, lean_object* v_q_221_){
_start:
{
lean_object* v___f_222_; 
v___f_222_ = ((lean_object*)(lp_tree_RingCon_mk_x27___at___00RingCon_mk_u2090___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__2_spec__6___closed__0));
return v___f_222_;
}
}
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0___boxed(lean_object* v_p_223_, lean_object* v_q_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = lp_tree_UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0(v_p_223_, v_q_224_);
lean_dec(v_q_224_);
lean_dec(v_p_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0(lean_object* v_p_231_, lean_object* v_q_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = ((lean_object*)(lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___closed__1));
return v___f_233_;
}
}
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0___boxed(lean_object* v_p_234_, lean_object* v_q_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0(v_p_234_, v_q_235_);
lean_dec(v_q_235_);
lean_dec(v_p_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ug_u03b9(lean_object* v_p_237_, lean_object* v_q_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lp_tree_UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0(v_p_237_, v_q_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ug_u03b9___boxed(lean_object* v_p_240_, lean_object* v_q_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_tree_Formalism_MainNotions_SchurIrreducible_ug_u03b9(v_p_240_, v_q_241_);
lean_dec(v_q_241_);
lean_dec(v_p_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1(lean_object* v_p_243_, lean_object* v_q_244_, lean_object* v_00_u03c6_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(v___f_246_, 0, v_00_u03c6_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1___boxed(lean_object* v_p_247_, lean_object* v_q_248_, lean_object* v_00_u03c6_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = lp_tree_AlgHom_toLinearMap___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__1(v_p_247_, v_q_248_, v_00_u03c6_249_);
lean_dec(v_q_248_);
lean_dec(v_p_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1(lean_object* v_p_251_, lean_object* v_q_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* lp_tree_UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1___boxed(lean_object* v_p_254_, lean_object* v_q_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = lp_tree_UniversalEnvelopingAlgebra_ringCon___at___00UniversalEnvelopingAlgebra_mkAlgHom___at___00UniversalEnvelopingAlgebra_00_u03b9___at___00Formalism_MainNotions_SchurIrreducible_ug_u03b9_spec__0_spec__0_spec__1(v_p_254_, v_q_255_);
lean_dec(v_q_255_);
lean_dec(v_p_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_SchurIrreducible_UgF_spec__0(lean_object* v_p_257_, lean_object* v_q_258_, lean_object* v_s_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_SchurIrreducible_UgF_spec__0___boxed(lean_object* v_p_261_, lean_object* v_q_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = lp_tree_Submodule_span___at___00Formalism_MainNotions_SchurIrreducible_UgF_spec__0(v_p_261_, v_q_262_, v_s_263_);
lean_dec(v_q_262_);
lean_dec(v_p_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___redArg(lean_object* v_p_265_, lean_object* v_q_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___redArg___boxed(lean_object* v_p_268_, lean_object* v_q_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___redArg(v_p_268_, v_q_269_);
lean_dec(v_q_269_);
lean_dec(v_p_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF(lean_object* v_p_271_, lean_object* v_q_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_UgF___boxed(lean_object* v_p_275_, lean_object* v_q_276_, lean_object* v_k_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = lp_tree_Formalism_MainNotions_SchurIrreducible_UgF(v_p_275_, v_q_276_, v_k_277_);
lean_dec(v_k_277_);
lean_dec(v_q_276_);
lean_dec(v_p_275_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indRel(lean_object* v_p_279_, lean_object* v_q_280_, lean_object* v_V_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_act_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indRel___boxed(lean_object* v_p_286_, lean_object* v_q_287_, lean_object* v_V_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_act_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_tree_Formalism_MainNotions_SchurIrreducible_indRel(v_p_286_, v_q_287_, v_V_288_, v_inst_289_, v_inst_290_, v_act_291_);
lean_dec(v_act_291_);
lean_dec(v_inst_290_);
lean_dec_ref(v_inst_289_);
lean_dec(v_q_287_);
lean_dec(v_p_286_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indF(lean_object* v_p_293_, lean_object* v_q_294_, lean_object* v_V_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_act_298_, lean_object* v_k_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indF___boxed(lean_object* v_p_301_, lean_object* v_q_302_, lean_object* v_V_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_act_306_, lean_object* v_k_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_tree_Formalism_MainNotions_SchurIrreducible_indF(v_p_301_, v_q_302_, v_V_303_, v_inst_304_, v_inst_305_, v_act_306_, v_k_307_);
lean_dec(v_k_307_);
lean_dec(v_act_306_);
lean_dec(v_inst_305_);
lean_dec_ref(v_inst_304_);
lean_dec(v_q_302_);
lean_dec(v_p_301_);
return v_res_308_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg___lam__0(lean_object* v_p_309_, lean_object* v_q_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_313_, 0, v_p_309_);
v___x_314_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_314_, 0, v_q_310_);
v___x_315_ = l_instDecidableEqSum_decEq___redArg(v___x_313_, v___x_314_, v_a_311_, v_b_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg___lam__0___boxed(lean_object* v_p_316_, lean_object* v_q_317_, lean_object* v_a_318_, lean_object* v_b_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg___lam__0(v_p_316_, v_q_317_, v_a_318_, v_b_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg(lean_object* v_p_322_, lean_object* v_q_323_, lean_object* v_inst_324_, lean_object* v_inst_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_toSemiring_328_; lean_object* v_toSemiring_329_; lean_object* v___x_330_; lean_object* v_toAddMonoid_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_toSMul_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_toAddCommGroup_342_; lean_object* v___x_343_; lean_object* v_toSMul_344_; lean_object* v___x_345_; lean_object* v_toSemiring_346_; lean_object* v_toAddCommMonoid_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_toSupSet_354_; lean_object* v___x_355_; 
v___x_326_ = lp_mathlib_Complex_instCommSemiring;
v___x_327_ = lp_mathlib_Complex_commRing;
v_toSemiring_328_ = lean_ctor_get(v___x_327_, 0);
v_toSemiring_329_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_toSemiring_328_);
v___x_330_ = lp_mathlib_Algebra_id___redArg(v_toSemiring_328_);
v_toAddMonoid_331_ = lean_ctor_get(v_inst_324_, 0);
lean_inc_ref_n(v_toAddMonoid_331_, 2);
lean_dec_ref(v_inst_324_);
lean_inc(v_q_323_);
lean_inc(v_p_322_);
v___f_332_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_332_, 0, v_p_322_);
lean_closure_set(v___f_332_, 1, v_q_323_);
v___x_333_ = l_List_finRange(v_p_322_);
v___x_334_ = l_List_finRange(v_q_323_);
v___x_335_ = lp_mathlib_Multiset_disjSum___redArg(v___x_333_, v___x_334_);
lean_inc_ref(v___f_332_);
v___x_336_ = lp_mathlib_Matrix_instRing___redArg(v___x_335_, v___f_332_, v___x_327_);
v___x_337_ = lp_mathlib_LieRing_ofAssociativeRing___redArg(v___x_336_);
lean_dec_ref(v___x_336_);
lean_inc_ref(v_toSemiring_329_);
v___x_338_ = lp_mathlib_Matrix_instAlgebra___redArg(v___f_332_, v_toSemiring_329_, v___x_330_);
v_toSMul_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc_n(v_toSMul_339_, 2);
lean_dec_ref(v___x_338_);
lean_inc_ref(v___x_337_);
v___x_340_ = lp_mathlib_instRingUniversalEnvelopingAlgebra___redArg(v___x_327_, v___x_337_, v_toSMul_339_);
v___x_341_ = lp_mathlib_LieRing_ofAssociativeRing___redArg(v___x_340_);
v_toAddCommGroup_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_toAddCommGroup_342_);
lean_dec_ref(v___x_341_);
v___x_343_ = lp_mathlib_instAlgebraUniversalEnvelopingAlgebra___redArg(v___x_327_, v___x_337_, v_toSMul_339_);
v_toSMul_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_n(v_toSMul_344_, 3);
lean_dec_ref(v___x_343_);
lean_inc(v_inst_325_);
v___x_345_ = lp_mathlib_TensorProduct_addCommGroup___redArg(v___x_326_, v_toAddCommGroup_342_, v_toAddMonoid_331_, v_toSMul_344_, v_inst_325_);
v_toSemiring_346_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_toSemiring_346_);
lean_dec_ref(v___x_340_);
v_toAddCommMonoid_347_ = lean_ctor_get(v_toSemiring_346_, 0);
lean_inc_ref(v_toAddCommMonoid_347_);
lean_dec_ref(v_toSemiring_346_);
v___f_348_ = lean_alloc_closure((void*)(lp_mathlib_TensorProduct_leftHasSMul___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_348_, 0, v___x_326_);
lean_closure_set(v___f_348_, 1, v_toAddCommMonoid_347_);
lean_closure_set(v___f_348_, 2, v_toAddMonoid_331_);
lean_closure_set(v___f_348_, 3, v_toSMul_344_);
lean_closure_set(v___f_348_, 4, v_inst_325_);
lean_closure_set(v___f_348_, 5, v_toSMul_344_);
v___x_349_ = lean_box(0);
lean_inc_ref(v___f_348_);
v___x_350_ = lp_mathlib_Submodule_Quotient_addMonoid___redArg(v___x_327_, v___x_345_, v___f_348_, v___x_349_);
v___f_351_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_Quotient_instSMul_x27___redArg___lam__0), 3, 1);
lean_closure_set(v___f_351_, 0, v___f_348_);
v___x_352_ = lp_mathlib_Submodule_completeLattice___redArg(v___x_326_, v___x_350_, v___f_351_);
lean_dec_ref(v___f_351_);
lean_dec_ref(v___x_350_);
v___x_353_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_352_);
v_toSupSet_354_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_toSupSet_354_);
lean_dec_ref(v___x_353_);
v___x_355_ = lean_apply_1(v_toSupSet_354_, lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt(lean_object* v_p_356_, lean_object* v_q_357_, lean_object* v_V_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_act_361_, lean_object* v_k_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___redArg(v_p_356_, v_q_357_, v_inst_359_, v_inst_360_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt___boxed(lean_object* v_p_364_, lean_object* v_q_365_, lean_object* v_V_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_act_369_, lean_object* v_k_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = lp_tree_Formalism_MainNotions_SchurIrreducible_indFlt(v_p_364_, v_q_365_, v_V_366_, v_inst_367_, v_inst_368_, v_act_369_, v_k_370_);
lean_dec(v_k_370_);
lean_dec(v_act_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___lam__0(lean_object* v_O_372_, lean_object* v_00_u03c0_373_, lean_object* v_f_u2081_374_, lean_object* v_f_u2082_375_, lean_object* v_00_u03c6_u2081_376_, lean_object* v_00_u03c6_u2082_377_, lean_object* v_s_378_, lean_object* v_v_379_){
_start:
{
lean_object* v_Zv_380_; lean_object* v___x_381_; 
v_Zv_380_ = lean_ctor_get(v_O_372_, 15);
lean_inc_ref(v_Zv_380_);
lean_dec_ref(v_O_372_);
v___x_381_ = lean_apply_7(v_Zv_380_, v_00_u03c0_373_, v_f_u2081_374_, v_f_u2082_375_, v_00_u03c6_u2081_376_, v_00_u03c6_u2082_377_, v_v_379_, v_s_378_);
return v___x_381_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___closed__0(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lp_mathlib_Complex_commRing;
v___x_383_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg(lean_object* v_O_384_, lean_object* v_00_u03c0_385_, lean_object* v_f_u2081_386_, lean_object* v_f_u2082_387_, lean_object* v_00_u03c6_u2081_388_, lean_object* v_00_u03c6_u2082_389_, lean_object* v_S_390_, lean_object* v_s_391_){
_start:
{
lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___f_392_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___lam__0), 8, 7);
lean_closure_set(v___f_392_, 0, v_O_384_);
lean_closure_set(v___f_392_, 1, v_00_u03c0_385_);
lean_closure_set(v___f_392_, 2, v_f_u2081_386_);
lean_closure_set(v___f_392_, 3, v_f_u2082_387_);
lean_closure_set(v___f_392_, 4, v_00_u03c6_u2081_388_);
lean_closure_set(v___f_392_, 5, v_00_u03c6_u2082_389_);
lean_closure_set(v___f_392_, 6, v_s_391_);
v___x_393_ = lean_obj_once(&lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___closed__0, &lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg___closed__0);
v___x_394_ = lp_mathlib_Finset_prod___redArg(v___x_393_, v_S_390_, v___f_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS(lean_object* v_F_395_, lean_object* v_E_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_A_403_, lean_object* v_B_404_, lean_object* v_O_405_, lean_object* v_00_u03c0_406_, lean_object* v_f_u2081_407_, lean_object* v_f_u2082_408_, lean_object* v_00_u03c6_u2081_409_, lean_object* v_00_u03c6_u2082_410_, lean_object* v_S_411_, lean_object* v_s_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___redArg(v_O_405_, v_00_u03c0_406_, v_f_u2081_407_, v_f_u2082_408_, v_00_u03c6_u2081_409_, v_00_u03c6_u2082_410_, v_S_411_, v_s_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SchurIrreducible_ZS___boxed(lean_object** _args){
lean_object* v_F_414_ = _args[0];
lean_object* v_E_415_ = _args[1];
lean_object* v_inst_416_ = _args[2];
lean_object* v_inst_417_ = _args[3];
lean_object* v_inst_418_ = _args[4];
lean_object* v_inst_419_ = _args[5];
lean_object* v_inst_420_ = _args[6];
lean_object* v_inst_421_ = _args[7];
lean_object* v_A_422_ = _args[8];
lean_object* v_B_423_ = _args[9];
lean_object* v_O_424_ = _args[10];
lean_object* v_00_u03c0_425_ = _args[11];
lean_object* v_f_u2081_426_ = _args[12];
lean_object* v_f_u2082_427_ = _args[13];
lean_object* v_00_u03c6_u2081_428_ = _args[14];
lean_object* v_00_u03c6_u2082_429_ = _args[15];
lean_object* v_S_430_ = _args[16];
lean_object* v_s_431_ = _args[17];
_start:
{
lean_object* v_res_432_; 
v_res_432_ = lp_tree_Formalism_MainNotions_SchurIrreducible_ZS(v_F_414_, v_E_415_, v_inst_416_, v_inst_417_, v_inst_418_, v_inst_419_, v_inst_420_, v_inst_421_, v_A_422_, v_B_423_, v_O_424_, v_00_u03c0_425_, v_f_u2081_426_, v_f_u2082_427_, v_00_u03c6_u2081_428_, v_00_u03c6_u2082_429_, v_S_430_, v_s_431_);
lean_dec_ref(v_B_423_);
lean_dec_ref(v_A_422_);
lean_dec_ref(v_inst_421_);
lean_dec(v_inst_420_);
lean_dec_ref(v_inst_418_);
lean_dec_ref(v_inst_416_);
return v_res_432_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataTheta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_SchurIrreducible(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
