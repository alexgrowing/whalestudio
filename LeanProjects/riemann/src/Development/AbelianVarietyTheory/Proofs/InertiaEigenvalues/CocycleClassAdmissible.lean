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

theorem GlobalTheory.admissible_eventually_iff_mem_cls : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  intro l _ P S M _ _ W X _ _ _ hX hlev z
  constructor
  · rintro ⟨a₀, h⟩
    obtain ⟨a₁, h1⟩ := hX
    have hle1 : a₁ ≤ max a₀ (max a₁ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    have ha : ∀ x : X, S.Γ.lam ^ (max a₀ (max a₁ 1)) • x = 0 := by
      intro x
      rw [← Nat.sub_add_cancel hle1, pow_add, mul_smul, h1, smul_zero]
    have hA := h (max a₀ (max a₁ 1)) (le_max_left _ _) ha
    have hone : 1 ≤ max a₀ (max a₁ 1) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hlev _ ha hone]
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mpr hA
  · intro h
    refine ⟨1, fun a ha1 ha => ?_⟩
    rw [hlev a ha ha1] at h
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mp h
