// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.DefGroup
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel public import Formalism.SatakeDualWeyl.DefsCS public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
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
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_ring___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_SubgroupClass_toGroup___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_toHomUnits___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Pi_evalMulHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_MonoidHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_instCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_det(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_inclusion___lam__0___boxed(lean_object*);
lean_object* l_Fin_castLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blockTri(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blockTri___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_blkMat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_blkMat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_blkMat___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_blkMat___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_DIV_blkMat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_blkMat___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_DIV_blkMat___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_DIV_blkMat___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_DIV_blkMat___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_blkDet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkDet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_blkDet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_blkDet___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_blkDet___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkDet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkDet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipCol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeHom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_supHom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_supHom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipSym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symHom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_UR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_UR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_full___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_full(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_full___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_LevelP_prj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_LevelP_prj___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_inclusion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_lev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_lev___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levX___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levV___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkExp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkExp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkExp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkNum___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkNum(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2___redArg(lean_object* v_r_1_, lean_object* v_a_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_a_2_, v_r_1_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(1u);
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(0u);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2___redArg___boxed(lean_object* v_r_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_L2_DIV_blk2___redArg(v_r_6_, v_a_7_);
lean_dec(v_a_7_);
lean_dec(v_r_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2(lean_object* v_n_9_, lean_object* v_r_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_L2_DIV_blk2___redArg(v_r_10_, v_a_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blk2___boxed(lean_object* v_n_13_, lean_object* v_r_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_L2_DIV_blk2(v_n_13_, v_r_14_, v_a_15_);
lean_dec(v_a_15_);
lean_dec(v_r_14_);
lean_dec(v_n_13_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf___redArg(lean_object* v_r_17_, lean_object* v_t_18_, lean_object* v_a_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_nat_dec_lt(v_a_19_, v_r_17_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_21_ = lean_nat_sub(v_a_19_, v_r_17_);
v___x_22_ = lean_nat_div(v___x_21_, v_t_18_);
lean_dec(v___x_21_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(0u);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf___redArg___boxed(lean_object* v_r_26_, lean_object* v_t_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_L2_DIV_blkOf___redArg(v_r_26_, v_t_27_, v_a_28_);
lean_dec(v_a_28_);
lean_dec(v_t_27_);
lean_dec(v_r_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf(lean_object* v_n_30_, lean_object* v_r_31_, lean_object* v_t_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_L2_DIV_blkOf___redArg(v_r_31_, v_t_32_, v_a_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkOf___boxed(lean_object* v_n_35_, lean_object* v_r_36_, lean_object* v_t_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_L2_DIV_blkOf(v_n_35_, v_r_36_, v_t_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec(v_t_37_);
lean_dec(v_r_36_);
lean_dec(v_n_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blockTri(lean_object* v_00_u03ba_40_, lean_object* v_inst_41_, lean_object* v_n_42_, lean_object* v_b_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blockTri___boxed(lean_object* v_00_u03ba_45_, lean_object* v_inst_46_, lean_object* v_n_47_, lean_object* v_b_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_L2_DIV_blockTri(v_00_u03ba_45_, v_inst_46_, v_n_47_, v_b_48_);
lean_dec_ref(v_b_48_);
lean_dec(v_n_47_);
lean_dec_ref(v_inst_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___lam__0(lean_object* v_self_50_){
_start:
{
lean_inc(v_self_50_);
return v_self_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___lam__0___boxed(lean_object* v_self_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_tree_Formalism_L2_DIV_blkMat___lam__0(v_self_51_);
lean_dec(v_self_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___lam__1(lean_object* v___f_53_, lean_object* v_g_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_val_57_; lean_object* v___x_58_; 
v_val_57_ = lean_ctor_get(v_g_54_, 0);
lean_inc(v_val_57_);
lean_dec_ref(v_g_54_);
lean_inc_ref(v___f_53_);
v___x_58_ = lp_mathlib_Matrix_submatrix___redArg(v_val_57_, v___f_53_, v___f_53_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat(lean_object* v_00_u03ba_62_, lean_object* v_inst_63_, lean_object* v_n_64_, lean_object* v_b_65_, lean_object* v_c_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_blkMat___closed__1));
return v___f_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkMat___boxed(lean_object* v_00_u03ba_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_b_71_, lean_object* v_c_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_tree_Formalism_L2_DIV_blkMat(v_00_u03ba_68_, v_inst_69_, v_n_70_, v_b_71_, v_c_72_);
lean_dec(v_c_72_);
lean_dec_ref(v_b_71_);
lean_dec(v_n_70_);
lean_dec_ref(v_inst_69_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_blkDet___redArg___lam__0(lean_object* v_b_74_, lean_object* v_c_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_apply_1(v_b_74_, v_a_76_);
v___x_78_ = lean_nat_dec_eq(v___x_77_, v_c_75_);
lean_dec(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkDet___redArg___lam__0___boxed(lean_object* v_b_79_, lean_object* v_c_80_, lean_object* v_a_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = lp_tree_Formalism_L2_DIV_blkDet___redArg___lam__0(v_b_79_, v_c_80_, v_a_81_);
lean_dec(v_c_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkDet___redArg(lean_object* v_inst_85_, lean_object* v_n_86_, lean_object* v_b_87_, lean_object* v_c_88_){
_start:
{
lean_object* v_toSemiring_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_toMonoid_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___x_102_; 
v_toSemiring_89_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_n(v_n_86_, 2);
v___x_90_ = l_List_finRange(v_n_86_);
v___x_91_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_91_, 0, v_n_86_);
lean_inc(v___x_90_);
lean_inc_ref(v_toSemiring_89_);
v___x_92_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_89_, v___x_90_, v___x_91_);
v_toMonoid_93_ = lean_ctor_get(v___x_92_, 1);
lean_inc_ref(v_toMonoid_93_);
lean_dec_ref(v___x_92_);
lean_inc(v_c_88_);
lean_inc_ref(v_b_87_);
v___f_94_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_blkDet___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_94_, 0, v_b_87_);
lean_closure_set(v___f_94_, 1, v_c_88_);
v___f_95_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_blkDet___redArg___closed__0));
v___x_96_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_93_);
v___x_97_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_96_);
v___x_98_ = lp_mathlib_Subtype_fintype___redArg(v___f_94_, v___x_90_);
lean_inc_ref(v_inst_85_);
v___x_99_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_det), 6, 5);
lean_closure_set(v___x_99_, 0, lean_box(0));
lean_closure_set(v___x_99_, 1, v___f_95_);
lean_closure_set(v___x_99_, 2, v___x_98_);
lean_closure_set(v___x_99_, 3, lean_box(0));
lean_closure_set(v___x_99_, 4, v_inst_85_);
v___x_100_ = lp_tree_Formalism_L2_DIV_blkMat(lean_box(0), v_inst_85_, v_n_86_, v_b_87_, v_c_88_);
lean_dec(v_c_88_);
lean_dec_ref(v_b_87_);
lean_dec(v_n_86_);
lean_dec_ref(v_inst_85_);
v___f_101_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_101_, 0, v___x_100_);
lean_closure_set(v___f_101_, 1, v___x_99_);
v___x_102_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_97_, v___f_101_);
lean_dec_ref(v___x_97_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkDet(lean_object* v_00_u03ba_103_, lean_object* v_inst_104_, lean_object* v_n_105_, lean_object* v_b_106_, lean_object* v_c_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lp_tree_Formalism_L2_DIV_blkDet___redArg(v_inst_104_, v_n_105_, v_b_106_, v_c_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkR___redArg___lam__0(lean_object* v_r_109_, lean_object* v_n_110_, lean_object* v_g_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_val_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_val_114_ = lean_ctor_get(v_g_111_, 0);
lean_inc(v_val_114_);
lean_dec_ref(v_g_111_);
v___x_115_ = lean_alloc_closure((void*)(l_Fin_castLE___boxed), 4, 3);
lean_closure_set(v___x_115_, 0, v_r_109_);
lean_closure_set(v___x_115_, 1, v_n_110_);
lean_closure_set(v___x_115_, 2, lean_box(0));
lean_inc_ref(v___x_115_);
v___x_116_ = lp_mathlib_Matrix_submatrix___redArg(v_val_114_, v___x_115_, v___x_115_, v___y_112_, v___y_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkR___redArg(lean_object* v_inst_117_, lean_object* v_n_118_, lean_object* v_r_119_){
_start:
{
lean_object* v_toSemiring_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_toMonoid_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_toSemiring_120_ = lean_ctor_get(v_inst_117_, 0);
lean_inc_ref(v_toSemiring_120_);
lean_dec_ref(v_inst_117_);
lean_inc_n(v_n_118_, 2);
v___x_121_ = l_List_finRange(v_n_118_);
v___x_122_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_122_, 0, v_n_118_);
v___x_123_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_120_, v___x_121_, v___x_122_);
v_toMonoid_124_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_toMonoid_124_);
lean_dec_ref(v___x_123_);
v___f_125_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_blkR___redArg___lam__0), 5, 2);
lean_closure_set(v___f_125_, 0, v_r_119_);
lean_closure_set(v___f_125_, 1, v_n_118_);
v___x_126_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_124_);
v___x_127_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_126_);
v___x_128_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_127_, v___f_125_);
lean_dec_ref(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_blkR(lean_object* v_00_u03ba_129_, lean_object* v_inst_130_, lean_object* v_n_131_, lean_object* v_r_132_, lean_object* v_hr_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lp_tree_Formalism_L2_DIV_blkR___redArg(v_inst_130_, v_n_131_, v_r_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unip(lean_object* v_00_u03ba_135_, lean_object* v_inst_136_, lean_object* v_r_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unip___boxed(lean_object* v_00_u03ba_139_, lean_object* v_inst_140_, lean_object* v_r_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_tree_Formalism_L2_DIV_unip(v_00_u03ba_139_, v_inst_140_, v_r_141_);
lean_dec(v_r_141_);
lean_dec_ref(v_inst_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipCol(lean_object* v_00_u03ba_143_, lean_object* v_inst_144_, lean_object* v_r_145_, lean_object* v_a_146_, lean_object* v_c_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipCol___boxed(lean_object* v_00_u03ba_149_, lean_object* v_inst_150_, lean_object* v_r_151_, lean_object* v_a_152_, lean_object* v_c_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_tree_Formalism_L2_DIV_unipCol(v_00_u03ba_149_, v_inst_150_, v_r_151_, v_a_152_, v_c_153_);
lean_dec(v_c_153_);
lean_dec(v_a_152_);
lean_dec(v_r_151_);
lean_dec_ref(v_inst_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__0(lean_object* v_inst_155_, lean_object* v_i_156_, lean_object* v_toSemiring_157_, lean_object* v_g_158_, lean_object* v_j_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
lean_inc(v_j_159_);
lean_inc(v_i_156_);
v___x_160_ = lean_apply_2(v_inst_155_, v_i_156_, v_j_159_);
v___x_161_ = lean_unbox(v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v_toZero_163_; 
lean_dec(v_j_159_);
lean_dec_ref(v_g_158_);
lean_dec(v_i_156_);
v___x_162_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_157_);
v_toZero_163_ = lean_ctor_get(v___x_162_, 1);
lean_inc(v_toZero_163_);
lean_dec_ref(v___x_162_);
return v_toZero_163_;
}
else
{
lean_object* v_val_164_; lean_object* v___x_165_; 
lean_dec_ref(v_toSemiring_157_);
v_val_164_ = lean_ctor_get(v_g_158_, 0);
lean_inc(v_val_164_);
lean_dec_ref(v_g_158_);
v___x_165_ = lean_apply_2(v_val_164_, v_i_156_, v_j_159_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__1(lean_object* v_inst_166_, lean_object* v_toSemiring_167_, lean_object* v_g_168_, lean_object* v_toAddCommMonoid_169_, lean_object* v___x_170_, lean_object* v_i_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; 
v___f_172_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__0), 5, 4);
lean_closure_set(v___f_172_, 0, v_inst_166_);
lean_closure_set(v___f_172_, 1, v_i_171_);
lean_closure_set(v___f_172_, 2, v_toSemiring_167_);
lean_closure_set(v___f_172_, 3, v_g_168_);
v___x_173_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_169_, v___x_170_, v___f_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__1___boxed(lean_object* v_inst_174_, lean_object* v_toSemiring_175_, lean_object* v_g_176_, lean_object* v_toAddCommMonoid_177_, lean_object* v___x_178_, lean_object* v_i_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__1(v_inst_174_, v_toSemiring_175_, v_g_176_, v_toAddCommMonoid_177_, v___x_178_, v_i_179_);
lean_dec_ref(v_toAddCommMonoid_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum___redArg(lean_object* v_inst_181_, lean_object* v_r_182_, lean_object* v_inst_183_, lean_object* v_g_184_){
_start:
{
lean_object* v_toSemiring_185_; lean_object* v_toAddCommMonoid_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
v_toSemiring_185_ = lean_ctor_get(v_inst_181_, 0);
lean_inc_ref(v_toSemiring_185_);
lean_dec_ref(v_inst_181_);
v_toAddCommMonoid_186_ = lean_ctor_get(v_toSemiring_185_, 0);
lean_inc_ref_n(v_toAddCommMonoid_186_, 2);
v___x_187_ = l_List_finRange(v_r_182_);
lean_inc(v___x_187_);
v___f_188_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_edgeSum___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_188_, 0, v_inst_183_);
lean_closure_set(v___f_188_, 1, v_toSemiring_185_);
lean_closure_set(v___f_188_, 2, v_g_184_);
lean_closure_set(v___f_188_, 3, v_toAddCommMonoid_186_);
lean_closure_set(v___f_188_, 4, v___x_187_);
v___x_189_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_186_, v___x_187_, v___f_188_);
lean_dec_ref(v_toAddCommMonoid_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeSum(lean_object* v_00_u03ba_190_, lean_object* v_inst_191_, lean_object* v_r_192_, lean_object* v_Ed_193_, lean_object* v_inst_194_, lean_object* v_g_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lp_tree_Formalism_L2_DIV_edgeSum___redArg(v_inst_191_, v_r_192_, v_inst_194_, v_g_195_);
return v___x_196_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg(lean_object* v_i_197_, lean_object* v_j_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_add(v_i_197_, v___x_199_);
v___x_201_ = lean_nat_dec_eq(v_j_198_, v___x_200_);
lean_dec(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg___boxed(lean_object* v_i_202_, lean_object* v_j_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg(v_i_202_, v_j_203_);
lean_dec(v_j_203_);
lean_dec(v_i_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1(lean_object* v_r_206_, lean_object* v_i_207_, lean_object* v_j_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg(v_i_207_, v_j_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___boxed(lean_object* v_r_210_, lean_object* v_i_211_, lean_object* v_j_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1(v_r_210_, v_i_211_, v_j_212_);
lean_dec(v_j_212_);
lean_dec(v_i_211_);
lean_dec(v_r_210_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___redArg(lean_object* v_i_215_, lean_object* v_j_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg(v_i_215_, v_j_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___redArg___boxed(lean_object* v_i_218_, lean_object* v_j_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___redArg(v_i_218_, v_j_219_);
lean_dec(v_j_219_);
lean_dec(v_i_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge(lean_object* v_r_222_, lean_object* v_i_223_, lean_object* v_j_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___aux__1___redArg(v_i_223_, v_j_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___boxed(lean_object* v_r_226_, lean_object* v_i_227_, lean_object* v_j_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge(v_r_226_, v_i_227_, v_j_228_);
lean_dec(v_j_228_);
lean_dec(v_i_227_);
lean_dec(v_r_226_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg(lean_object* v_00_u03c1_231_, lean_object* v_k_232_, lean_object* v_i_233_, lean_object* v_j_234_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_i_233_, v___x_241_);
v___x_243_ = lean_nat_dec_eq(v_j_234_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v___x_242_);
goto v___jp_235_;
}
else
{
uint8_t v___x_244_; 
v___x_244_ = lean_nat_dec_eq(v___x_242_, v_00_u03c1_231_);
if (v___x_244_ == 0)
{
if (v___x_243_ == 0)
{
lean_dec(v___x_242_);
goto v___jp_235_;
}
else
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_nat_add(v_00_u03c1_231_, v_k_232_);
v___x_246_ = lean_nat_dec_eq(v___x_242_, v___x_245_);
lean_dec(v___x_245_);
lean_dec(v___x_242_);
if (v___x_246_ == 0)
{
return v___x_243_;
}
else
{
goto v___jp_235_;
}
}
}
else
{
lean_dec(v___x_242_);
goto v___jp_235_;
}
}
v___jp_235_:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_i_233_, v___x_236_);
v___x_238_ = lean_nat_dec_eq(v___x_237_, v_00_u03c1_231_);
lean_dec(v___x_237_);
if (v___x_238_ == 0)
{
return v___x_238_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_nat_add(v_00_u03c1_231_, v_k_232_);
v___x_240_ = lean_nat_dec_eq(v_j_234_, v___x_239_);
lean_dec(v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg___boxed(lean_object* v_00_u03c1_247_, lean_object* v_k_248_, lean_object* v_i_249_, lean_object* v_j_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg(v_00_u03c1_247_, v_k_248_, v_i_249_, v_j_250_);
lean_dec(v_j_250_);
lean_dec(v_i_249_);
lean_dec(v_k_248_);
lean_dec(v_00_u03c1_247_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1(lean_object* v_r_253_, lean_object* v_00_u03c1_254_, lean_object* v_k_255_, lean_object* v_i_256_, lean_object* v_j_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg(v_00_u03c1_254_, v_k_255_, v_i_256_, v_j_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___boxed(lean_object* v_r_259_, lean_object* v_00_u03c1_260_, lean_object* v_k_261_, lean_object* v_i_262_, lean_object* v_j_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1(v_r_259_, v_00_u03c1_260_, v_k_261_, v_i_262_, v_j_263_);
lean_dec(v_j_263_);
lean_dec(v_i_262_);
lean_dec(v_k_261_);
lean_dec(v_00_u03c1_260_);
lean_dec(v_r_259_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___redArg(lean_object* v_00_u03c1_266_, lean_object* v_k_267_, lean_object* v_i_268_, lean_object* v_j_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg(v_00_u03c1_266_, v_k_267_, v_i_268_, v_j_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___redArg___boxed(lean_object* v_00_u03c1_271_, lean_object* v_k_272_, lean_object* v_i_273_, lean_object* v_j_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___redArg(v_00_u03c1_271_, v_k_272_, v_i_273_, v_j_274_);
lean_dec(v_j_274_);
lean_dec(v_i_273_);
lean_dec(v_k_272_);
lean_dec(v_00_u03c1_271_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge(lean_object* v_r_277_, lean_object* v_00_u03c1_278_, lean_object* v_k_279_, lean_object* v_i_280_, lean_object* v_j_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___aux__1___redArg(v_00_u03c1_278_, v_k_279_, v_i_280_, v_j_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___boxed(lean_object* v_r_283_, lean_object* v_00_u03c1_284_, lean_object* v_k_285_, lean_object* v_i_286_, lean_object* v_j_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge(v_r_283_, v_00_u03c1_284_, v_k_285_, v_i_286_, v_j_287_);
lean_dec(v_j_287_);
lean_dec(v_i_286_);
lean_dec(v_k_285_);
lean_dec(v_00_u03c1_284_);
lean_dec(v_r_283_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0(lean_object* v_inst_291_, lean_object* v_r_292_, lean_object* v_inst_293_, lean_object* v_g_294_){
_start:
{
lean_object* v___x_295_; lean_object* v_toFun_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_295_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0___closed__0);
v_toFun_296_ = lean_ctor_get(v___x_295_, 0);
v___x_297_ = lp_tree_Formalism_L2_DIV_edgeSum___redArg(v_inst_291_, v_r_292_, v_inst_293_, v_g_294_);
lean_inc(v_toFun_296_);
v___x_298_ = lean_apply_1(v_toFun_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeHom___redArg(lean_object* v_inst_299_, lean_object* v_r_300_, lean_object* v_inst_301_){
_start:
{
lean_object* v___f_302_; 
v___f_302_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0), 4, 3);
lean_closure_set(v___f_302_, 0, v_inst_299_);
lean_closure_set(v___f_302_, 1, v_r_300_);
lean_closure_set(v___f_302_, 2, v_inst_301_);
return v___f_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_edgeHom(lean_object* v_00_u03ba_303_, lean_object* v_inst_304_, lean_object* v_r_305_, lean_object* v_Ed_306_, lean_object* v_inst_307_, lean_object* v_H_308_, lean_object* v_hone_309_, lean_object* v_hadd_310_){
_start:
{
lean_object* v___f_311_; 
v___f_311_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0), 4, 3);
lean_closure_set(v___f_311_, 0, v_inst_304_);
lean_closure_set(v___f_311_, 1, v_r_305_);
lean_closure_set(v___f_311_, 2, v_inst_307_);
return v___f_311_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_supHom___redArg(lean_object* v_inst_312_, lean_object* v_r_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___f_315_; 
lean_inc(v_r_313_);
v___x_314_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_instDecidableRelFinSupEdge___boxed), 3, 1);
lean_closure_set(v___x_314_, 0, v_r_313_);
v___f_315_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0), 4, 3);
lean_closure_set(v___f_315_, 0, v_inst_312_);
lean_closure_set(v___f_315_, 1, v_r_313_);
lean_closure_set(v___f_315_, 2, v___x_314_);
return v___f_315_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_supHom(lean_object* v_00_u03ba_316_, lean_object* v_inst_317_, lean_object* v_r_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lp_tree_Formalism_L2_DIV_supHom___redArg(v_inst_317_, v_r_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipSym(lean_object* v_00_u03ba_320_, lean_object* v_inst_321_, lean_object* v_r_322_, lean_object* v_00_u03c1_323_, lean_object* v_k_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_unipSym___boxed(lean_object* v_00_u03ba_326_, lean_object* v_inst_327_, lean_object* v_r_328_, lean_object* v_00_u03c1_329_, lean_object* v_k_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = lp_tree_Formalism_L2_DIV_unipSym(v_00_u03ba_326_, v_inst_327_, v_r_328_, v_00_u03c1_329_, v_k_330_);
lean_dec(v_k_330_);
lean_dec(v_00_u03c1_329_);
lean_dec(v_r_328_);
lean_dec_ref(v_inst_327_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symHom___redArg(lean_object* v_inst_332_, lean_object* v_r_333_, lean_object* v_00_u03c1_334_, lean_object* v_k_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___f_337_; 
lean_inc(v_r_333_);
v___x_336_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_instDecidableRelFinSymEdge___boxed), 5, 3);
lean_closure_set(v___x_336_, 0, v_r_333_);
lean_closure_set(v___x_336_, 1, v_00_u03c1_334_);
lean_closure_set(v___x_336_, 2, v_k_335_);
v___f_337_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_edgeHom___redArg___lam__0), 4, 3);
lean_closure_set(v___f_337_, 0, v_inst_332_);
lean_closure_set(v___f_337_, 1, v_r_333_);
lean_closure_set(v___f_337_, 2, v___x_336_);
return v___f_337_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_symHom(lean_object* v_00_u03ba_338_, lean_object* v_inst_339_, lean_object* v_r_340_, lean_object* v_00_u03c1_341_, lean_object* v_k_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lp_tree_Formalism_L2_DIV_symHom___redArg(v_inst_339_, v_r_340_, v_00_u03c1_341_, v_k_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom___redArg(lean_object* v_inst_344_, lean_object* v_00_u03c8_345_, lean_object* v_f_346_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; 
v___f_347_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_347_, 0, v_f_346_);
lean_closure_set(v___f_347_, 1, v_00_u03c8_345_);
v___x_348_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v_inst_344_, v___f_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom___redArg___boxed(lean_object* v_inst_349_, lean_object* v_00_u03c8_350_, lean_object* v_f_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = lp_tree_Formalism_L2_DIV_addCharHom___redArg(v_inst_349_, v_00_u03c8_350_, v_f_351_);
lean_dec_ref(v_inst_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom(lean_object* v_00_u03ba_353_, lean_object* v_inst_354_, lean_object* v_LL_355_, lean_object* v_inst_356_, lean_object* v_G_357_, lean_object* v_inst_358_, lean_object* v_00_u03c8_359_, lean_object* v_f_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lp_tree_Formalism_L2_DIV_addCharHom___redArg(v_inst_358_, v_00_u03c8_359_, v_f_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_addCharHom___boxed(lean_object* v_00_u03ba_362_, lean_object* v_inst_363_, lean_object* v_LL_364_, lean_object* v_inst_365_, lean_object* v_G_366_, lean_object* v_inst_367_, lean_object* v_00_u03c8_368_, lean_object* v_f_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lp_tree_Formalism_L2_DIV_addCharHom(v_00_u03ba_362_, v_inst_363_, v_LL_364_, v_inst_365_, v_G_366_, v_inst_367_, v_00_u03c8_368_, v_f_369_);
lean_dec_ref(v_inst_367_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_363_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_UR(lean_object* v_F_371_, lean_object* v_E_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_n_379_, lean_object* v_hc_380_, lean_object* v_J_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(0);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_UR___boxed(lean_object* v_F_383_, lean_object* v_E_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_n_391_, lean_object* v_hc_392_, lean_object* v_J_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = lp_tree_Formalism_L2_DIV_UR(v_F_383_, v_E_384_, v_inst_385_, v_inst_386_, v_inst_387_, v_inst_388_, v_inst_389_, v_inst_390_, v_n_391_, v_hc_392_, v_J_393_);
lean_dec(v_J_393_);
lean_dec(v_n_391_);
lean_dec_ref(v_inst_390_);
lean_dec(v_inst_389_);
lean_dec_ref(v_inst_387_);
lean_dec_ref(v_inst_385_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0(lean_object* v_toMonoid_395_, lean_object* v_x_396_){
_start:
{
lean_object* v___x_397_; lean_object* v_toOne_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v___x_397_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_395_);
v_toOne_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_397_, 1);
lean_dec(v_unused_406_);
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_toOne_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
lean_inc(v_toOne_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_toOne_398_);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_toOne_398_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_toOne_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0___boxed(lean_object* v_toMonoid_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0(v_toMonoid_407_, v_x_408_);
lean_dec_ref(v_x_408_);
lean_dec_ref(v_toMonoid_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___redArg(lean_object* v_inst_410_){
_start:
{
lean_object* v_toSemiring_411_; lean_object* v_toMonoid_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_toSemiring_411_ = lean_ctor_get(v_inst_410_, 0);
lean_inc_ref(v_toSemiring_411_);
lean_dec_ref(v_inst_410_);
v_toMonoid_412_ = lean_ctor_get(v_toSemiring_411_, 1);
lean_inc_ref(v_toMonoid_412_);
lean_dec_ref(v_toSemiring_411_);
v___f_413_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_413_, 0, v_toMonoid_412_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___f_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv(lean_object* v_E_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_Pg_419_, lean_object* v_r_420_, lean_object* v_LL_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lp_tree_Formalism_L2_DIV_LevelP_triv___redArg(v_inst_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_triv___boxed(lean_object* v_E_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_Pg_427_, lean_object* v_r_428_, lean_object* v_LL_429_, lean_object* v_inst_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = lp_tree_Formalism_L2_DIV_LevelP_triv(v_E_424_, v_inst_425_, v_inst_426_, v_Pg_427_, v_r_428_, v_LL_429_, v_inst_430_);
lean_dec(v_r_428_);
lean_dec(v_Pg_427_);
lean_dec_ref(v_inst_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_full___redArg(lean_object* v_inst_432_){
_start:
{
lean_object* v_toSemiring_433_; lean_object* v_toMonoid_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_toSemiring_433_ = lean_ctor_get(v_inst_432_, 0);
lean_inc_ref(v_toSemiring_433_);
lean_dec_ref(v_inst_432_);
v_toMonoid_434_ = lean_ctor_get(v_toSemiring_433_, 1);
lean_inc_ref(v_toMonoid_434_);
lean_dec_ref(v_toSemiring_433_);
v___f_435_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_LevelP_triv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_435_, 0, v_toMonoid_434_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___f_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_full(lean_object* v_E_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_Pg_441_, lean_object* v_r_442_, lean_object* v_LL_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lp_tree_Formalism_L2_DIV_LevelP_full___redArg(v_inst_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_full___boxed(lean_object* v_E_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_Pg_449_, lean_object* v_r_450_, lean_object* v_LL_451_, lean_object* v_inst_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = lp_tree_Formalism_L2_DIV_LevelP_full(v_E_446_, v_inst_447_, v_inst_448_, v_Pg_449_, v_r_450_, v_LL_451_, v_inst_452_);
lean_dec(v_r_450_);
lean_dec(v_Pg_449_);
lean_dec_ref(v_inst_447_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj___redArg___lam__0(lean_object* v_chi_454_, lean_object* v_g_455_){
_start:
{
lean_object* v___x_456_; lean_object* v_val_457_; lean_object* v_inv_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v___x_456_ = lean_apply_1(v_chi_454_, v_g_455_);
v_val_457_ = lean_ctor_get(v___x_456_, 0);
v_inv_458_ = lean_ctor_get(v___x_456_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_456_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_inv_458_);
lean_inc(v_val_457_);
lean_dec(v___x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_val_457_);
lean_ctor_set(v___x_460_, 0, v_inv_458_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_inv_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_val_457_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj___redArg(lean_object* v_P_466_){
_start:
{
lean_object* v_H_467_; lean_object* v_chi_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_476_; 
v_H_467_ = lean_ctor_get(v_P_466_, 0);
v_chi_468_ = lean_ctor_get(v_P_466_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_P_466_);
if (v_isSharedCheck_476_ == 0)
{
v___x_470_ = v_P_466_;
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_chi_468_);
lean_inc(v_H_467_);
lean_dec(v_P_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___f_472_; lean_object* v___x_474_; 
v___f_472_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_LevelP_conj___redArg___lam__0), 2, 1);
lean_closure_set(v___f_472_, 0, v_chi_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___f_472_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_H_467_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___f_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj(lean_object* v_E_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_Pg_480_, lean_object* v_r_481_, lean_object* v_LL_482_, lean_object* v_inst_483_, lean_object* v_P_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lp_tree_Formalism_L2_DIV_LevelP_conj___redArg(v_P_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_conj___boxed(lean_object* v_E_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_Pg_489_, lean_object* v_r_490_, lean_object* v_LL_491_, lean_object* v_inst_492_, lean_object* v_P_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = lp_tree_Formalism_L2_DIV_LevelP_conj(v_E_486_, v_inst_487_, v_inst_488_, v_Pg_489_, v_r_490_, v_LL_491_, v_inst_492_, v_P_493_);
lean_dec_ref(v_inst_492_);
lean_dec(v_r_490_);
lean_dec(v_Pg_489_);
lean_dec_ref(v_inst_487_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj___redArg(lean_object* v_PP_496_){
_start:
{
lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___f_499_; lean_object* v___f_500_; 
v___f_497_ = lean_alloc_closure((void*)(lp_mathlib_Pi_evalMulHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_497_, 0, v_PP_496_);
v___f_498_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_LevelP_prj___redArg___closed__0));
v___f_499_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_499_, 0, v___f_498_);
lean_closure_set(v___f_499_, 1, v___f_497_);
v___f_500_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_500_, 0, v___f_499_);
return v___f_500_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj(lean_object* v_E_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_Pg_504_, lean_object* v_r_505_, lean_object* v_Hl_506_, lean_object* v_PP_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lp_tree_Formalism_L2_DIV_LevelP_prj___redArg(v_PP_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_prj___boxed(lean_object* v_E_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_Pg_512_, lean_object* v_r_513_, lean_object* v_Hl_514_, lean_object* v_PP_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = lp_tree_Formalism_L2_DIV_LevelP_prj(v_E_509_, v_inst_510_, v_inst_511_, v_Pg_512_, v_r_513_, v_Hl_514_, v_PP_515_);
lean_dec_ref(v_Hl_514_);
lean_dec(v_r_513_);
lean_dec(v_Pg_512_);
lean_dec_ref(v_inst_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg___lam__0(lean_object* v_cl_517_, lean_object* v_PP_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_apply_1(v_cl_517_, v_PP_518_);
v___x_521_ = lp_tree_Formalism_L2_DIV_LevelP_prj___redArg(v_PP_518_);
v___x_522_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___x_521_, v___x_520_, v___y_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(lean_object* v_Pg_523_, lean_object* v_inst_524_, lean_object* v_cl_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_toMonoid_528_; lean_object* v___f_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_526_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_524_);
v___x_527_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_526_);
v_toMonoid_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_toMonoid_528_);
lean_dec_ref(v___x_527_);
v___f_529_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg___lam__0), 3, 1);
lean_closure_set(v___f_529_, 0, v_cl_525_);
v___x_530_ = lean_box(0);
v___x_531_ = lp_mathlib_MonoidHom_instCommMonoid___redArg(v_toMonoid_528_);
v___x_532_ = lp_mathlib_Multiset_attach___redArg(v_Pg_523_);
v___x_533_ = lp_mathlib_Finset_prod___redArg(v___x_531_, v___x_532_, v___f_529_);
lean_dec_ref(v___x_531_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_530_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg___boxed(lean_object* v_Pg_535_, lean_object* v_inst_536_, lean_object* v_cl_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(v_Pg_535_, v_inst_536_, v_cl_537_);
lean_dec_ref(v_inst_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal(lean_object* v_E_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_Pg_542_, lean_object* v_r_543_, lean_object* v_LL_544_, lean_object* v_inst_545_, lean_object* v_Hl_546_, lean_object* v_cl_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(v_Pg_542_, v_inst_545_, v_cl_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LevelP_ofLocal___boxed(lean_object* v_E_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_Pg_552_, lean_object* v_r_553_, lean_object* v_LL_554_, lean_object* v_inst_555_, lean_object* v_Hl_556_, lean_object* v_cl_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = lp_tree_Formalism_L2_DIV_LevelP_ofLocal(v_E_549_, v_inst_550_, v_inst_551_, v_Pg_552_, v_r_553_, v_LL_554_, v_inst_555_, v_Hl_556_, v_cl_557_);
lean_dec_ref(v_Hl_556_);
lean_dec_ref(v_inst_555_);
lean_dec(v_r_553_);
lean_dec_ref(v_inst_550_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___redArg___lam__0(lean_object* v___x_559_, lean_object* v_r_560_, lean_object* v___x_561_, lean_object* v_00_u03c8_562_, lean_object* v_PP_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_565_; lean_object* v_toSemiring_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_toMonoid_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_52__overap_574_; lean_object* v___x_575_; 
v___x_565_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_559_, v_PP_563_);
v_toSemiring_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_toSemiring_566_);
lean_inc(v_r_560_);
v___x_567_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_567_, 0, v_r_560_);
v___x_568_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_566_, v___x_561_, v___x_567_);
v_toMonoid_569_ = lean_ctor_get(v___x_568_, 1);
lean_inc_ref(v_toMonoid_569_);
lean_dec_ref(v___x_568_);
v___x_570_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_569_);
v___x_571_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_570_);
v___x_572_ = lean_apply_1(v_00_u03c8_562_, v_PP_563_);
v___x_573_ = lp_tree_Formalism_L2_DIV_supHom___redArg(v___x_565_, v_r_560_);
v___x_52__overap_574_ = lp_tree_Formalism_L2_DIV_addCharHom___redArg(v___x_571_, v___x_572_, v___x_573_);
lean_dec_ref(v___x_571_);
v___x_575_ = lean_apply_1(v___x_52__overap_574_, v___y_564_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___redArg(lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_Pg_578_, lean_object* v_r_579_, lean_object* v_00_u03c8_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
v___x_581_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_576_);
lean_inc(v_r_579_);
v___x_582_ = l_List_finRange(v_r_579_);
v___f_583_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_P0___redArg___lam__0), 6, 4);
lean_closure_set(v___f_583_, 0, v___x_581_);
lean_closure_set(v___f_583_, 1, v_r_579_);
lean_closure_set(v___f_583_, 2, v___x_582_);
lean_closure_set(v___f_583_, 3, v_00_u03c8_580_);
v___x_584_ = lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(v_Pg_578_, v_inst_577_, v___f_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___redArg___boxed(lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_Pg_587_, lean_object* v_r_588_, lean_object* v_00_u03c8_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = lp_tree_Formalism_L2_DIV_P0___redArg(v_inst_585_, v_inst_586_, v_Pg_587_, v_r_588_, v_00_u03c8_589_);
lean_dec_ref(v_inst_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0(lean_object* v_E_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_LL_594_, lean_object* v_inst_595_, lean_object* v_Pg_596_, lean_object* v_r_597_, lean_object* v_00_u03c8_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lp_tree_Formalism_L2_DIV_P0___redArg(v_inst_592_, v_inst_595_, v_Pg_596_, v_r_597_, v_00_u03c8_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_P0___boxed(lean_object* v_E_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_LL_603_, lean_object* v_inst_604_, lean_object* v_Pg_605_, lean_object* v_r_606_, lean_object* v_00_u03c8_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = lp_tree_Formalism_L2_DIV_P0(v_E_600_, v_inst_601_, v_inst_602_, v_LL_603_, v_inst_604_, v_Pg_605_, v_r_606_, v_00_u03c8_607_);
lean_dec_ref(v_inst_604_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0(lean_object* v___x_610_, lean_object* v_r_611_, lean_object* v___x_612_, lean_object* v_00_u03c8_613_, lean_object* v_PP_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_616_; lean_object* v_toSemiring_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_toMonoid_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___f_626_; lean_object* v___x_627_; 
v___x_616_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_610_, v_PP_614_);
v_toSemiring_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_toSemiring_617_);
lean_inc(v_r_611_);
v___x_618_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_618_, 0, v_r_611_);
v___x_619_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_617_, v___x_612_, v___x_618_);
v_toMonoid_620_ = lean_ctor_get(v___x_619_, 1);
lean_inc_ref(v_toMonoid_620_);
lean_dec_ref(v___x_619_);
v___x_621_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_620_);
v___x_622_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_621_);
v___x_623_ = lean_apply_1(v_00_u03c8_613_, v_PP_614_);
v___x_624_ = lp_tree_Formalism_L2_DIV_supHom___redArg(v___x_616_, v_r_611_);
v___x_625_ = lp_tree_Formalism_L2_DIV_addCharHom___redArg(v___x_622_, v___x_623_, v___x_624_);
lean_dec_ref(v___x_622_);
v___f_626_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0___closed__0));
v___x_627_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_626_, v___x_625_, v___y_615_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg(lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_Pg_630_, lean_object* v_r_631_, lean_object* v_00_u03c8_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v___x_633_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_628_);
lean_inc(v_r_631_);
v___x_634_ = l_List_finRange(v_r_631_);
v___f_635_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_Psharp___redArg___lam__0), 6, 4);
lean_closure_set(v___f_635_, 0, v___x_633_);
lean_closure_set(v___f_635_, 1, v_r_631_);
lean_closure_set(v___f_635_, 2, v___x_634_);
lean_closure_set(v___f_635_, 3, v_00_u03c8_632_);
v___x_636_ = lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(v_Pg_630_, v_inst_629_, v___f_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___redArg___boxed(lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_Pg_639_, lean_object* v_r_640_, lean_object* v_00_u03c8_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = lp_tree_Formalism_L2_DIV_Psharp___redArg(v_inst_637_, v_inst_638_, v_Pg_639_, v_r_640_, v_00_u03c8_641_);
lean_dec_ref(v_inst_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp(lean_object* v_E_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_LL_646_, lean_object* v_inst_647_, lean_object* v_Pg_648_, lean_object* v_r_649_, lean_object* v_k_650_, lean_object* v_00_u03c8_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lp_tree_Formalism_L2_DIV_Psharp___redArg(v_inst_644_, v_inst_647_, v_Pg_648_, v_r_649_, v_00_u03c8_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Psharp___boxed(lean_object* v_E_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_LL_656_, lean_object* v_inst_657_, lean_object* v_Pg_658_, lean_object* v_r_659_, lean_object* v_k_660_, lean_object* v_00_u03c8_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = lp_tree_Formalism_L2_DIV_Psharp(v_E_653_, v_inst_654_, v_inst_655_, v_LL_656_, v_inst_657_, v_Pg_658_, v_r_659_, v_k_660_, v_00_u03c8_661_);
lean_dec(v_k_660_);
lean_dec_ref(v_inst_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___redArg___lam__0(lean_object* v___x_663_, lean_object* v_r_664_, lean_object* v___x_665_, lean_object* v_00_u03c8_666_, lean_object* v_00_u03c1_667_, lean_object* v_k_668_, lean_object* v_PP_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_671_; lean_object* v_toSemiring_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_toMonoid_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_52__overap_680_; lean_object* v___x_681_; 
v___x_671_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_663_, v_PP_669_);
v_toSemiring_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_toSemiring_672_);
lean_inc(v_r_664_);
v___x_673_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_673_, 0, v_r_664_);
v___x_674_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_672_, v___x_665_, v___x_673_);
v_toMonoid_675_ = lean_ctor_get(v___x_674_, 1);
lean_inc_ref(v_toMonoid_675_);
lean_dec_ref(v___x_674_);
v___x_676_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_675_);
v___x_677_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_676_);
v___x_678_ = lean_apply_1(v_00_u03c8_666_, v_PP_669_);
v___x_679_ = lp_tree_Formalism_L2_DIV_symHom___redArg(v___x_671_, v_r_664_, v_00_u03c1_667_, v_k_668_);
v___x_52__overap_680_ = lp_tree_Formalism_L2_DIV_addCharHom___redArg(v___x_677_, v___x_678_, v___x_679_);
lean_dec_ref(v___x_677_);
v___x_681_ = lean_apply_1(v___x_52__overap_680_, v___y_670_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___redArg(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_Pg_684_, lean_object* v_r_685_, lean_object* v_00_u03c1_686_, lean_object* v_k_687_, lean_object* v_00_u03c8_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___x_692_; 
v___x_689_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_682_);
lean_inc(v_r_685_);
v___x_690_ = l_List_finRange(v_r_685_);
v___f_691_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_PsharpSym___redArg___lam__0), 8, 6);
lean_closure_set(v___f_691_, 0, v___x_689_);
lean_closure_set(v___f_691_, 1, v_r_685_);
lean_closure_set(v___f_691_, 2, v___x_690_);
lean_closure_set(v___f_691_, 3, v_00_u03c8_688_);
lean_closure_set(v___f_691_, 4, v_00_u03c1_686_);
lean_closure_set(v___f_691_, 5, v_k_687_);
v___x_692_ = lp_tree_Formalism_L2_DIV_LevelP_ofLocal___redArg(v_Pg_684_, v_inst_683_, v___f_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___redArg___boxed(lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_Pg_695_, lean_object* v_r_696_, lean_object* v_00_u03c1_697_, lean_object* v_k_698_, lean_object* v_00_u03c8_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = lp_tree_Formalism_L2_DIV_PsharpSym___redArg(v_inst_693_, v_inst_694_, v_Pg_695_, v_r_696_, v_00_u03c1_697_, v_k_698_, v_00_u03c8_699_);
lean_dec_ref(v_inst_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym(lean_object* v_E_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_LL_704_, lean_object* v_inst_705_, lean_object* v_Pg_706_, lean_object* v_r_707_, lean_object* v_00_u03c1_708_, lean_object* v_k_709_, lean_object* v_00_u03c8_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lp_tree_Formalism_L2_DIV_PsharpSym___redArg(v_inst_702_, v_inst_705_, v_Pg_706_, v_r_707_, v_00_u03c1_708_, v_k_709_, v_00_u03c8_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_PsharpSym___boxed(lean_object* v_E_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_LL_715_, lean_object* v_inst_716_, lean_object* v_Pg_717_, lean_object* v_r_718_, lean_object* v_00_u03c1_719_, lean_object* v_k_720_, lean_object* v_00_u03c8_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = lp_tree_Formalism_L2_DIV_PsharpSym(v_E_712_, v_inst_713_, v_inst_714_, v_LL_715_, v_inst_716_, v_Pg_717_, v_r_718_, v_00_u03c1_719_, v_k_720_, v_00_u03c8_721_);
lean_dec_ref(v_inst_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_lev(lean_object* v_F_723_, lean_object* v_E_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_n_731_, lean_object* v_LL_732_, lean_object* v_inst_733_, lean_object* v_hc_734_, lean_object* v_J_735_, lean_object* v_00_u03b2_736_, lean_object* v_D_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_box(0);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_lev___boxed(lean_object* v_F_739_, lean_object* v_E_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_n_747_, lean_object* v_LL_748_, lean_object* v_inst_749_, lean_object* v_hc_750_, lean_object* v_J_751_, lean_object* v_00_u03b2_752_, lean_object* v_D_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = lp_tree_Formalism_L2_DIV_lev(v_F_739_, v_E_740_, v_inst_741_, v_inst_742_, v_inst_743_, v_inst_744_, v_inst_745_, v_inst_746_, v_n_747_, v_LL_748_, v_inst_749_, v_hc_750_, v_J_751_, v_00_u03b2_752_, v_D_753_);
lean_dec_ref(v_D_753_);
lean_dec_ref(v_00_u03b2_752_);
lean_dec(v_J_751_);
lean_dec_ref(v_inst_749_);
lean_dec(v_n_747_);
lean_dec_ref(v_inst_746_);
lean_dec(v_inst_745_);
lean_dec_ref(v_inst_743_);
lean_dec_ref(v_inst_741_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX___redArg___lam__0(lean_object* v_00_u03be_755_, lean_object* v_PP_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_758_; lean_object* v_val_759_; lean_object* v_inv_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v___x_758_ = lean_apply_2(v_00_u03be_755_, v_PP_756_, v___y_757_);
v_val_759_ = lean_ctor_get(v___x_758_, 0);
v_inv_760_ = lean_ctor_get(v___x_758_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_758_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_inv_760_);
lean_inc(v_val_759_);
lean_dec(v___x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v_val_759_);
lean_ctor_set(v___x_762_, 0, v_inv_760_);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_inv_760_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_val_759_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX___redArg(lean_object* v_r_768_, lean_object* v_t_769_, lean_object* v_m_770_, lean_object* v_Pg_771_, lean_object* v_Q_772_, lean_object* v_P_773_, lean_object* v_00_u03c7_774_, lean_object* v_00_u03be_775_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; 
v___f_776_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_datX___redArg___lam__0), 3, 1);
lean_closure_set(v___f_776_, 0, v_00_u03be_775_);
v___x_777_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_777_, 0, v_r_768_);
lean_ctor_set(v___x_777_, 1, v_t_769_);
lean_ctor_set(v___x_777_, 2, v_m_770_);
lean_ctor_set(v___x_777_, 3, v_Pg_771_);
lean_ctor_set(v___x_777_, 4, v_Q_772_);
lean_ctor_set(v___x_777_, 5, v_P_773_);
lean_ctor_set(v___x_777_, 6, v_00_u03c7_774_);
lean_ctor_set(v___x_777_, 7, v___f_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX(lean_object* v_E_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_LL_781_, lean_object* v_inst_782_, lean_object* v_r_783_, lean_object* v_t_784_, lean_object* v_m_785_, lean_object* v_Pg_786_, lean_object* v_Q_787_, lean_object* v_P_788_, lean_object* v_00_u03c7_789_, lean_object* v_00_u03be_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lp_tree_Formalism_L2_DIV_datX___redArg(v_r_783_, v_t_784_, v_m_785_, v_Pg_786_, v_Q_787_, v_P_788_, v_00_u03c7_789_, v_00_u03be_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datX___boxed(lean_object* v_E_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_LL_795_, lean_object* v_inst_796_, lean_object* v_r_797_, lean_object* v_t_798_, lean_object* v_m_799_, lean_object* v_Pg_800_, lean_object* v_Q_801_, lean_object* v_P_802_, lean_object* v_00_u03c7_803_, lean_object* v_00_u03be_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = lp_tree_Formalism_L2_DIV_datX(v_E_792_, v_inst_793_, v_inst_794_, v_LL_795_, v_inst_796_, v_r_797_, v_t_798_, v_m_799_, v_Pg_800_, v_Q_801_, v_P_802_, v_00_u03c7_803_, v_00_u03be_804_);
lean_dec_ref(v_inst_796_);
lean_dec_ref(v_inst_793_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___redArg___lam__0(lean_object* v_00_u03c7_806_, lean_object* v_j_807_, lean_object* v_x_808_, lean_object* v_PP_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_811_; lean_object* v_val_812_; lean_object* v_inv_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v___x_811_ = lean_apply_3(v_00_u03c7_806_, v_j_807_, v_PP_809_, v___y_810_);
v_val_812_ = lean_ctor_get(v___x_811_, 0);
v_inv_813_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_811_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_inv_813_);
lean_inc(v_val_812_);
lean_dec(v___x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_val_812_);
lean_ctor_set(v___x_815_, 0, v_inv_813_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_inv_813_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_val_812_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___redArg___lam__0___boxed(lean_object* v_00_u03c7_821_, lean_object* v_j_822_, lean_object* v_x_823_, lean_object* v_PP_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = lp_tree_Formalism_L2_DIV_datV___redArg___lam__0(v_00_u03c7_821_, v_j_822_, v_x_823_, v_PP_824_, v___y_825_);
lean_dec(v_x_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___redArg(lean_object* v_r_827_, lean_object* v_t_828_, lean_object* v_j_829_, lean_object* v_Pg_830_, lean_object* v_Q_831_, lean_object* v_P_832_, lean_object* v_00_u03c7_833_, lean_object* v_00_u03be_834_){
_start:
{
lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___f_835_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_datV___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_835_, 0, v_00_u03c7_833_);
lean_closure_set(v___f_835_, 1, v_j_829_);
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lp_tree_Formalism_L2_DIV_LevelP_conj___redArg(v_P_832_);
v___x_838_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_838_, 0, v_r_827_);
lean_ctor_set(v___x_838_, 1, v_t_828_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
lean_ctor_set(v___x_838_, 3, v_Pg_830_);
lean_ctor_set(v___x_838_, 4, v_Q_831_);
lean_ctor_set(v___x_838_, 5, v___x_837_);
lean_ctor_set(v___x_838_, 6, v___f_835_);
lean_ctor_set(v___x_838_, 7, v_00_u03be_834_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV(lean_object* v_E_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_LL_842_, lean_object* v_inst_843_, lean_object* v_r_844_, lean_object* v_t_845_, lean_object* v_j_846_, lean_object* v_Pg_847_, lean_object* v_Q_848_, lean_object* v_P_849_, lean_object* v_00_u03c7_850_, lean_object* v_00_u03be_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lp_tree_Formalism_L2_DIV_datV___redArg(v_r_844_, v_t_845_, v_j_846_, v_Pg_847_, v_Q_848_, v_P_849_, v_00_u03c7_850_, v_00_u03be_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_datV___boxed(lean_object* v_E_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_LL_856_, lean_object* v_inst_857_, lean_object* v_r_858_, lean_object* v_t_859_, lean_object* v_j_860_, lean_object* v_Pg_861_, lean_object* v_Q_862_, lean_object* v_P_863_, lean_object* v_00_u03c7_864_, lean_object* v_00_u03be_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = lp_tree_Formalism_L2_DIV_datV(v_E_853_, v_inst_854_, v_inst_855_, v_LL_856_, v_inst_857_, v_r_858_, v_t_859_, v_j_860_, v_Pg_861_, v_Q_862_, v_P_863_, v_00_u03c7_864_, v_00_u03be_865_);
lean_dec_ref(v_inst_857_);
lean_dec_ref(v_inst_854_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levX(lean_object* v_F_867_, lean_object* v_E_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_LL_875_, lean_object* v_inst_876_, lean_object* v_hc_877_, lean_object* v_r_878_, lean_object* v_t_879_, lean_object* v_m_880_, lean_object* v_J_881_, lean_object* v_00_u03b2_882_, lean_object* v_Pg_883_, lean_object* v_Q_884_, lean_object* v_P_885_, lean_object* v_00_u03c7_886_, lean_object* v_00_u03be_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_box(0);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levX___boxed(lean_object** _args){
lean_object* v_F_889_ = _args[0];
lean_object* v_E_890_ = _args[1];
lean_object* v_inst_891_ = _args[2];
lean_object* v_inst_892_ = _args[3];
lean_object* v_inst_893_ = _args[4];
lean_object* v_inst_894_ = _args[5];
lean_object* v_inst_895_ = _args[6];
lean_object* v_inst_896_ = _args[7];
lean_object* v_LL_897_ = _args[8];
lean_object* v_inst_898_ = _args[9];
lean_object* v_hc_899_ = _args[10];
lean_object* v_r_900_ = _args[11];
lean_object* v_t_901_ = _args[12];
lean_object* v_m_902_ = _args[13];
lean_object* v_J_903_ = _args[14];
lean_object* v_00_u03b2_904_ = _args[15];
lean_object* v_Pg_905_ = _args[16];
lean_object* v_Q_906_ = _args[17];
lean_object* v_P_907_ = _args[18];
lean_object* v_00_u03c7_908_ = _args[19];
lean_object* v_00_u03be_909_ = _args[20];
_start:
{
lean_object* v_res_910_; 
v_res_910_ = lp_tree_Formalism_L2_DIV_levX(v_F_889_, v_E_890_, v_inst_891_, v_inst_892_, v_inst_893_, v_inst_894_, v_inst_895_, v_inst_896_, v_LL_897_, v_inst_898_, v_hc_899_, v_r_900_, v_t_901_, v_m_902_, v_J_903_, v_00_u03b2_904_, v_Pg_905_, v_Q_906_, v_P_907_, v_00_u03c7_908_, v_00_u03be_909_);
lean_dec_ref(v_00_u03be_909_);
lean_dec_ref(v_00_u03c7_908_);
lean_dec_ref(v_P_907_);
lean_dec(v_Q_906_);
lean_dec(v_Pg_905_);
lean_dec_ref(v_00_u03b2_904_);
lean_dec(v_J_903_);
lean_dec(v_m_902_);
lean_dec(v_t_901_);
lean_dec(v_r_900_);
lean_dec_ref(v_inst_898_);
lean_dec_ref(v_inst_896_);
lean_dec(v_inst_895_);
lean_dec_ref(v_inst_893_);
lean_dec_ref(v_inst_891_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levV(lean_object* v_F_911_, lean_object* v_E_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_LL_919_, lean_object* v_inst_920_, lean_object* v_hc_921_, lean_object* v_r_922_, lean_object* v_t_923_, lean_object* v_j_924_, lean_object* v_J_925_, lean_object* v_00_u03b2_926_, lean_object* v_Pg_927_, lean_object* v_Q_928_, lean_object* v_P_929_, lean_object* v_00_u03c7_930_, lean_object* v_00_u03be_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_box(0);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_levV___boxed(lean_object** _args){
lean_object* v_F_933_ = _args[0];
lean_object* v_E_934_ = _args[1];
lean_object* v_inst_935_ = _args[2];
lean_object* v_inst_936_ = _args[3];
lean_object* v_inst_937_ = _args[4];
lean_object* v_inst_938_ = _args[5];
lean_object* v_inst_939_ = _args[6];
lean_object* v_inst_940_ = _args[7];
lean_object* v_LL_941_ = _args[8];
lean_object* v_inst_942_ = _args[9];
lean_object* v_hc_943_ = _args[10];
lean_object* v_r_944_ = _args[11];
lean_object* v_t_945_ = _args[12];
lean_object* v_j_946_ = _args[13];
lean_object* v_J_947_ = _args[14];
lean_object* v_00_u03b2_948_ = _args[15];
lean_object* v_Pg_949_ = _args[16];
lean_object* v_Q_950_ = _args[17];
lean_object* v_P_951_ = _args[18];
lean_object* v_00_u03c7_952_ = _args[19];
lean_object* v_00_u03be_953_ = _args[20];
_start:
{
lean_object* v_res_954_; 
v_res_954_ = lp_tree_Formalism_L2_DIV_levV(v_F_933_, v_E_934_, v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_inst_939_, v_inst_940_, v_LL_941_, v_inst_942_, v_hc_943_, v_r_944_, v_t_945_, v_j_946_, v_J_947_, v_00_u03b2_948_, v_Pg_949_, v_Q_950_, v_P_951_, v_00_u03c7_952_, v_00_u03be_953_);
lean_dec_ref(v_00_u03be_953_);
lean_dec_ref(v_00_u03c7_952_);
lean_dec_ref(v_P_951_);
lean_dec(v_Q_950_);
lean_dec(v_Pg_949_);
lean_dec_ref(v_00_u03b2_948_);
lean_dec(v_J_947_);
lean_dec(v_j_946_);
lean_dec(v_t_945_);
lean_dec(v_r_944_);
lean_dec_ref(v_inst_942_);
lean_dec_ref(v_inst_940_);
lean_dec(v_inst_939_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_935_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkExp___lam__0(lean_object* v_p_955_, lean_object* v___x_956_, lean_object* v_N_957_, lean_object* v_i_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_959_ = lean_nat_pow(v_p_955_, v_i_958_);
v___x_960_ = lean_nat_sub(v_p_955_, v___x_956_);
v___x_961_ = lean_nat_mul(v___x_959_, v___x_960_);
lean_dec(v___x_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_nat_div(v_N_957_, v___x_961_);
lean_dec(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkExp___lam__0___boxed(lean_object* v_p_963_, lean_object* v___x_964_, lean_object* v_N_965_, lean_object* v_i_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = lp_tree_Formalism_L2_DIV_minkExp___lam__0(v_p_963_, v___x_964_, v_N_965_, v_i_966_);
lean_dec(v_i_966_);
lean_dec(v_N_965_);
lean_dec(v___x_964_);
lean_dec(v_p_963_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkExp(lean_object* v_N_968_, lean_object* v_p_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_970_ = lean_unsigned_to_nat(1u);
lean_inc(v_N_968_);
v___f_971_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_minkExp___lam__0___boxed), 4, 3);
lean_closure_set(v___f_971_, 0, v_p_969_);
lean_closure_set(v___f_971_, 1, v___x_970_);
lean_closure_set(v___f_971_, 2, v_N_968_);
v___x_972_ = lean_nat_add(v_N_968_, v___x_970_);
lean_dec(v_N_968_);
v___x_973_ = l_List_range(v___x_972_);
v___x_974_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_973_, v___f_971_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkNum___lam__0(lean_object* v_N_975_, lean_object* v_p_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc(v_p_976_);
v___x_977_ = lp_tree_Formalism_L2_DIV_minkExp(v_N_975_, v_p_976_);
v___x_978_ = lean_nat_pow(v_p_976_, v___x_977_);
lean_dec(v___x_977_);
lean_dec(v_p_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_minkNum(lean_object* v_N_979_){
_start:
{
lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_inc(v_N_979_);
v___f_980_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_minkNum___lam__0), 2, 1);
lean_closure_set(v___f_980_, 0, v_N_979_);
v___x_981_ = lean_unsigned_to_nat(2u);
v___x_982_ = lean_nat_add(v_N_979_, v___x_981_);
lean_dec(v_N_979_);
v___x_983_ = l_List_range(v___x_982_);
v___x_984_ = lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(v___x_983_);
v___x_985_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_984_, v___f_980_);
return v___x_985_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianColumns_InLocalDiscriminantKernel(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_DefsCS(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianColumns_InLocalDiscriminantKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_DefsCS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
