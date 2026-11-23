import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_cj_Qbar_eq : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x : ℂ, x ∈ Qbar → x ∈ M → cj M ρ x = cj Qbar ρ' x := by
  intro M ρ
  let L : IntermediateField ℚ ℂ := M ⊓ Qbar
  have h1 : L ≤ M := inf_le_left
  have h2 : L ≤ Qbar := inf_le_right
  letI : Algebra L Qbar := (IntermediateField.inclusion h2).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L Qbar := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    exact (map_ratCast (algebraMap ℚ ℂ) r).trans (by simp)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic L Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := L) (M := ℂ)
    (E := Qbar) (ρ.comp (IntermediateField.inclusion h1))
  refine ⟨φ, fun x hx hM => ?_⟩
  rw [cj_mem ρ hM, cj_mem φ hx]
  have := DFunLike.congr_fun hφ (⟨x, ⟨hM, hx⟩⟩ : L)
  exact this.symm

end GlobalTheory.ThetaConj
