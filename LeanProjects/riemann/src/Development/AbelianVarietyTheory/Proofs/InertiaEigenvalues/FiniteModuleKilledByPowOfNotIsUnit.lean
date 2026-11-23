import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem finite_module_killed_by_pow_of_not_isUnit :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  intro O _ _ lam hlam X _ _ _
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes (R := O) X lam
  set Y : Submodule O X := LinearMap.range (lam ^ n • (LinearMap.id : X →ₗ[O] X)) with hY
  have hFG : Y.FG := Module.Finite.iff_fg.mp inferInstance
  have hle : Y ≤ Ideal.span {lam} • Y := by
    intro y hy
    have hy' : y ∈ LinearMap.range (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) := by
      rw [← hn (n + 1) (Nat.le_succ n)]; exact hy
    obtain ⟨x, rfl⟩ := hy'
    have hmem : lam ^ n • x ∈ Y := ⟨x, by simp⟩
    have : (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) x = lam • (lam ^ n • x) := by
      simp [pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self lam) hmem
  have hjac : Ideal.span {lam} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal lam).mpr hlam
  have hbot : Y = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ Y hFG hle hjac
  refine ⟨n, fun x => ?_⟩
  have : lam ^ n • x ∈ Y := ⟨x, by simp⟩
  rw [hbot] at this
  simpa using this

end GlobalTheory
