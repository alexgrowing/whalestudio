import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar

namespace GlobalTheory

private theorem exists_real_scalar_of_selfAdjoint_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (σ g)) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have key : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨m, hxm, hmy⟩ : ∃ m : ℝ, x < m ∧ m < y := ⟨(x + y) / 2, by linarith, by linarith⟩
    have hfc : ContinuousOn (fun t : ℝ => max (t - m) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (t - m) 0).continuousOn
    have hkc : ContinuousOn (fun t : ℝ => max (m - t) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (m - t) 0).continuousOn
    have hprod : cfc (fun t : ℝ => max (t - m) 0) A * cfc (fun t : ℝ => max (m - t) 0) A = 0 := by
      rw [← cfc_mul _ _ A hfc hkc]
      have h0 : (fun t : ℝ => max (t - m) 0 * max (m - t) 0) = (0 : ℝ → ℝ) := by
        funext t
        rcases le_total t m with h | h
        · rw [max_eq_right (by linarith), zero_mul, Pi.zero_apply]
        · rw [max_eq_right (by linarith : m - t ≤ 0), mul_zero, Pi.zero_apply]
      rw [h0, cfc_zero]
    have hk0 : cfc (fun t : ℝ => max (m - t) 0) A ≠ 0 := by
      intro h0
      rw [← cfc_zero ℝ A] at h0
      have h1 := eqOn_of_cfc_eq_cfc h0 hkc continuousOn_const hA hx
      simp only [Pi.zero_apply] at h1
      have h2 : m - x ≤ max (m - x) 0 := le_max_left _ _
      linarith
    obtain ⟨w, hw⟩ : ∃ w, cfc (fun t : ℝ => max (m - t) 0) A w ≠ 0 := by
      by_contra hnot
      simp only [not_exists, not_not] at hnot
      exact hk0 (ContinuousLinearMap.ext hnot)
    let F := cfc (fun t : ℝ => max (t - m) 0) A
    let S : Submodule ℂ H := LinearMap.ker (F : H →ₗ[ℂ] H)
    have hS : IsClosed (S : Set H) := F.isClosed_ker
    have hinv : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
      intro g v hv
      have hv' : F v = 0 := hv
      have hcg : F * σ g = σ g * F := ((hc g).cfc_real _).eq
      change F (σ g v) = 0
      have := congrArg (fun L : H →L[ℂ] H => L v) hcg
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at this
      rw [this, hv', map_zero]
    have hmem : cfc (fun t : ℝ => max (m - t) 0) A w ∈ S := by
      change F (cfc (fun t : ℝ => max (m - t) 0) A w) = 0
      simpa [F] using congrArg (fun L : H →L[ℂ] H => L w) hprod
    rcases hirr S hS hinv with hbot | htop
    · rw [hbot, Submodule.mem_bot] at hmem
      exact hw hmem
    · have hF : F = 0 := by
        ext v
        have hv : v ∈ S := by rw [htop]; exact Submodule.mem_top
        exact hv
      rw [← cfc_zero ℝ A] at hF
      have h1 := eqOn_of_cfc_eq_cfc hF hfc continuousOn_const hA hy
      simp only [Pi.zero_apply] at h1
      have h2 : y - m ≤ max (y - m) 0 := le_max_left _ _
      linarith
  have hsub : ∃ c : ℝ, ∀ x ∈ spectrum ℝ A, x = c := by
    by_cases hne : (spectrum ℝ A).Nonempty
    · obtain ⟨c, hc'⟩ := hne
      refine ⟨c, fun x hx => ?_⟩
      rcases lt_trichotomy x c with h | h | h
      · exact (key x hx c hc' h).elim
      · exact h
      · exact (key c hc' x hx h).elim
    · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨c, hc'⟩ := hsub
  refine ⟨c, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hc' x hx
    _ = algebraMap ℝ (H →L[ℂ] H) c := cfc_const c A hA

theorem hilbert_schur_of_adjoint_closed :
    ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)), (∀ g, ∃ g', σ g' = ContinuousLinearMap.adjoint (σ g)) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ T : H →L[ℂ] H, (∀ g, T ∘L σ g = σ g ∘L T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  intro G H _ _ _ σ hadj hirr T hT
  have hcomm : ∀ g, Commute T (σ g) := fun g => hT g
  have hcomm' : ∀ g, Commute (star T) (σ g) := by
    intro g
    obtain ⟨g', hg'⟩ := hadj g
    have h1 := congrArg star (hcomm g').eq
    rw [star_mul, star_mul, hg', ← ContinuousLinearMap.star_eq_adjoint, star_star] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (realPart T : H →L[ℂ] H)
    (realPart T).prop fun g => by
      rw [realPart_apply_coe]
      exact ((hcomm g).add_left (hcomm' g)).smul_left _
  obtain ⟨b, hb⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (imaginaryPart T : H →L[ℂ] H)
    (imaginaryPart T).prop fun g => by
      rw [imaginaryPart_apply_coe]
      exact (((hcomm g).sub_left (hcomm' g)).smul_left _).smul_left _
  refine ⟨(a : ℂ) + Complex.I * b, ?_⟩
  calc T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
        (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((a : ℂ) + Complex.I * b) • (1 : H →L[ℂ] H) := by
        rw [ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul,
          mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
