import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FunctionFieldTrdeg

theorem trdeg_functionField_eq : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (s : G ⟶ Sp F) (d : ℕ), IsProjOver s → topologicalKrullDim G = d → ∀ (φ : F →+* G.functionField), G.fromSpecStalk (genericPoint G) ≫ s = spMap φ → (letI := φ.toAlgebra; Algebra.trdeg F G.functionField = d) := by
  intro F _ G _ s d hs hd φ hφ
  obtain ⟨N, i, hi, hcomp⟩ := hs
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType s := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ s)
  have hψ : Spec.map ψ = hU.fromSpec ≫ s := Spec.map_preimage _
  letI : Algebra F Γ(G, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(G, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(G, U) = d :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F s hU ⟨_, hxU⟩ d hd
  letI : Algebra F G.functionField := φ.toAlgebra
  have key : CommRingCat.ofHom φ = ψ ≫ G.germToFunctionField U := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ = _
    rw [← hφ, hψ, ← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc]
  haveI : IsScalarTower F Γ(G, U) G.functionField :=
    IsScalarTower.of_algebraMap_eq' congr($(key).hom)
  haveI := functionField_isFractionRing_of_isAffineOpen G U hU
  haveI : FaithfulSMul F Γ(G, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(G, U)).injective
  haveI : FaithfulSMul Γ(G, U) G.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Γ(G, U) G.functionField)
  haveI : Algebra.IsAlgebraic Γ(G, U) G.functionField := IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(G, U))
  show Algebra.trdeg F G.functionField = d
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top F Γ(G, U) G.functionField, hA]

end GlobalTheory.FunctionFieldTrdeg
