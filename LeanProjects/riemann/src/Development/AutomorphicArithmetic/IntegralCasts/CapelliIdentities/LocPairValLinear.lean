import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

theorem UpperTheory.Reformulated.B.Qp9.locPair_val_linear :
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] (K : Type) [Fintype K] [inst_4 : DecidableEq K] (ι : K → Type)
    [(k : K) → Fintype (ι k)] (σ : Type) [inst_6 : Fintype σ] (T : GlobalTheory.CompanionTheory.Ar.Num.LocPair ι O σ)
    (P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι O)),
    (∀ (Gs Hs : σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧
      (∀ (c : ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ (MvPolynomial.C : ℝ → MvPolynomial (σ ⊕ σ) ℝ) c * Gs i) = c * T.val P Gs) ∧
        ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ ∑ a ∈ s, Gs a i) =
            ∑ a ∈ s,
              T.val P
                (Gs
                  a) := by
  intro O _ _ _ K _ _ ι _ σ _ T P
  have key : ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, T.val P Gs = ∑ i, Finsupp.linearCombination ℝ
      (fun μ => (GlobalTheory.CompanionTheory.Ar.Num.cycList (GroundTheory.Heights₂.Heights.NumbersDVR.ratDiv P (T.f i) (T.g i))
        (GroundTheory.Heights₂.Heights.NumbersDVR.classList (Sum.elim T.x T.x') μ ++ []) : ℝ))
      (MvPolynomial.basisMonomials (σ ⊕ σ) ℝ |>.repr (Gs i)) := fun Gs => rfl
  refine ⟨fun Gs Hs => ?_, fun c Gs => ?_, fun α s Gs => ?_⟩
  · simp only [key, Pi.add_apply, map_add, Finset.sum_add_distrib]
  · simp only [key, MvPolynomial.C_mul', map_smul, smul_eq_mul, Finset.mul_sum]
  · simp only [key, map_sum]
    exact Finset.sum_comm
