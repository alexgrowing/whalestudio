import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open Formalism.MainNotions.S Matrix MeasureTheory

namespace GlobalTheory

theorem hilbert_schur_selfAdjoint (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, π g * A = A * π g) :
    ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  have hsub : (spectrum ℝ A).Subsingleton := by
    have key : ∀ a ∈ spectrum ℝ A, ∀ b ∈ spectrum ℝ A, ¬ a < b := by
      intro a ha b hb hab
      set m : ℝ := (a + b) / 2 with hm
      let f : ℝ → ℝ := fun x => max (m - x) 0
      let g : ℝ → ℝ := fun x => max (x - m) 0
      have hf : Continuous f := by fun_prop
      have hg : Continuous g := by fun_prop
      have hfg : cfc f A * cfc g A = 0 := by
        rw [← cfc_mul f g A hf.continuousOn hg.continuousOn]
        have : (fun x => f x * g x) = (0 : ℝ → ℝ) := by
          funext x
          simp only [f, g, Pi.zero_apply]
          rcases le_total x m with h | h
          · rw [max_eq_right (by linarith : x - m ≤ 0), mul_zero]
          · rw [max_eq_right (by linarith : m - x ≤ 0), zero_mul]
        rw [this, cfc_zero]
      have hne : ∀ (k : ℝ → ℝ), Continuous k → ∀ x ∈ spectrum ℝ A, k x ≠ 0 → cfc k A ≠ 0 := by
        intro k hk x hx hkx h0
        have h1 : cfc k A = cfc (0 : ℝ → ℝ) A := by rw [h0, cfc_zero]
        exact hkx (eqOn_of_cfc_eq_cfc h1 hk.continuousOn continuousOn_const hA hx)
      have hf0 : cfc f A ≠ 0 := hne f hf a ha (by
        have : 0 < m - a := by rw [hm]; linarith
        simp only [f]; rw [max_eq_left this.le]; exact this.ne')
      have hg0 : cfc g A ≠ 0 := hne g hg b hb (by
        have : 0 < b - m := by rw [hm]; linarith
        simp only [g]; rw [max_eq_left this.le]; exact this.ne')
      have hcomm : ∀ x, Commute (cfc f A) (π x) := fun x =>
        hA.commute_cfc (show Commute A (π x) from (hc x).symm) f
      rcases hirr (LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap) (cfc f A).isClosed_ker (by
        intro x v hv
        have hv' : cfc f A v = 0 := hv
        show cfc f A (π x v) = 0
        have := congrArg (fun T : H →L[ℂ] H => T v) (hcomm x).eq
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hv', map_zero]) with h | h
      · apply hg0
        ext v
        have : cfc g A v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap := by
          show cfc f A (cfc g A v) = 0
          have := congrArg (fun T : H →L[ℂ] H => T v) hfg
          simpa using this
        rw [h] at this
        simpa using this
      · apply hf0
        ext v
        have : v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap := by
          rw [h]; trivial
        exact this
    intro a ha b hb
    exact le_antisymm (not_lt.1 (key b hb a ha)) (not_lt.1 (key a ha b hb))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, spectrum ℝ A ⊆ {r} := by
    rcases hsub.eq_empty_or_singleton with h | ⟨r, h⟩
    · exact ⟨0, by rw [h]; exact Set.empty_subset _⟩
    · exact ⟨r, h.subset⟩
  refine ⟨r, ?_⟩
  rw [CFC.eq_algebraMap_of_spectrum_subset_singleton A r hr hA, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul]

theorem hilbert_schur :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ A : H →L[ℂ] H, (∀ g, π g * A = A * π g) → ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  intro H _ _ _ G _ π hn hirr A hc
  have hstar : ∀ g, star (π g) = π g⁻¹ := by
    intro g
    have h1 : star (π g) * π g = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (π g)).1 (hn g)
    calc star (π g) = star (π g) * (π g * π g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = π g⁻¹ := by rw [← mul_assoc, h1, one_mul]
  have hc' : ∀ g, π g * star A = star A * π g := by
    intro g
    have := congrArg star (hc g⁻¹)
    rw [star_mul, star_mul, hstar, inv_inv] at this
    exact this.symm
  obtain ⟨b, hb⟩ := hilbert_schur_selfAdjoint H G π hirr (A + star A)
    (IsSelfAdjoint.add_star_self A) (fun g => by rw [mul_add, add_mul, hc, hc'])
  obtain ⟨c, hc2⟩ := hilbert_schur_selfAdjoint H G π hirr (Complex.I • (A - star A))
    (by
      rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub])
    (fun g => by rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hc, hc'])
  refine ⟨(1 / 2 : ℂ) * (b - Complex.I * c), ?_⟩
  have h3 : A - star A = (-(Complex.I * c)) • (1 : H →L[ℂ] H) := by
    rw [neg_smul, mul_smul, ← hc2, smul_smul, Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  rw [mul_smul, sub_eq_add_neg, add_smul, ← hb, ← h3]
  module

end GlobalTheory
