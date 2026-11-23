import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeFromOrthogonality

noncomputable section

namespace PIW.HCFdeg

open scoped InnerProductSpace ComplexStarModule
open ContinuousLinearMap

section Schur

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : G →* (H →L[ℂ] H))

lemma adjoint_rep (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) : adjoint (π g) = π g⁻¹ := by
  have hinner : ∀ (h : G) (x y : H), ⟪π h x, π h y⟫_ℂ = ⟪x, y⟫_ℂ := fun h x y =>
    (⟨(π h).toLinearMap, hπ h⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  have hinv : ∀ x, π g (π g⁻¹ x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    simp
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  conv_rhs => rw [← hinv x]
  rw [hinner]

lemma commute_star (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (T : H →L[ℂ] H) (hT : ∀ g, Commute T (π g))
    (g : G) : Commute (star T) (π g) := by
  have h1 : star (π g⁻¹) = π g := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rep π hπ, inv_inv]
  have h2 : T * π g⁻¹ = π g⁻¹ * T := hT g⁻¹
  show star T * π g = π g * star T
  calc star T * π g = star T * star (π g⁻¹) := by rw [h1]
    _ = star (π g⁻¹ * T) := by rw [star_mul]
    _ = star (T * π g⁻¹) := by rw [h2]
    _ = star (π g⁻¹) * star T := by rw [star_mul]
    _ = π g * star T := by rw [h1]

lemma sa_scalar (hirr : Irr π) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hc : ∀ g, Commute A (π g)) : ∃ r : ℝ, A = algebraMap ℝ (H →L[ℂ] H) r := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · refine ⟨0, ?_⟩
    ext v
    exact Subsingleton.elim _ _
  obtain ⟨v0, hv0⟩ := exists_ne (0 : H)
  haveI : Nontrivial (H →L[ℂ] H) := ⟨⟨0, 1, fun h => hv0 (by
    have h1 := congrArg (fun T : H →L[ℂ] H => T v0) h
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply] at h1
    exact h1.symm)⟩⟩
  have hcom : ∀ (f : ℝ → ℝ) (g : G), Commute (cfc f A) (π g) := by
    intro f g
    first
    | exact (hc g).cfc_real f
    | exact Commute.cfc_real (hc g) f
    | exact (hc g).cfc (by rw [hA.star_eq]; exact hc g) f
    | exact Commute.cfc (hc g) (by rw [hA.star_eq]; exact hc g) f
  have hsub : ∀ s ∈ spectrum ℝ A, ∀ t ∈ spectrum ℝ A, s < t → False := by
    intro s hs t ht hst
    set m := (s + t) / 2 with hm
    let f : ℝ → ℝ := fun x => max 0 (m - x)
    let g : ℝ → ℝ := fun x => max 0 (x - m)
    have hf : Continuous f := by fun_prop
    have hg : Continuous g := by fun_prop
    have hgf : (fun x => g x * f x) = fun _ => (0 : ℝ) := by
      funext x
      rcases le_total x m with h | h
      · have : g x = 0 := max_eq_left (by linarith)
        rw [this, zero_mul]
      · have : f x = 0 := max_eq_left (by linarith)
        rw [this, mul_zero]
    have hYX : cfc g A * cfc f A = 0 := by
      rw [← cfc_mul g f A (hf := hg.continuousOn) (hg := hf.continuousOn), hgf,
        cfc_const (0 : ℝ) A, map_zero]
    have hne0 : ∀ (k : ℝ → ℝ), Continuous k → ∀ x ∈ spectrum ℝ A, k x ≠ 0 → cfc k A ≠ 0 := by
      intro k hk x hx hkx h0
      have h1 := cfc_map_spectrum k A (hf := hk.continuousOn)
      rw [h0, spectrum.zero_eq] at h1
      have h2 : k x ∈ k '' spectrum ℝ A := ⟨x, hx, rfl⟩
      rw [← h1] at h2
      exact hkx h2
    have hX : cfc f A ≠ 0 := hne0 f hf s hs (by
      show max 0 (m - s) ≠ 0
      rw [max_eq_right (by linarith)]
      linarith)
    have hY : cfc g A ≠ 0 := hne0 g hg t ht (by
      show max 0 (t - m) ≠ 0
      rw [max_eq_right (by linarith)]
      linarith)
    let S : Submodule ℂ H := LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H)
    have hSc : IsClosed (S : Set H) := ContinuousLinearMap.isClosed_ker (cfc g A)
    have hSi : ∀ g' : G, ∀ v ∈ S, π g' v ∈ S := by
      intro g' v hv
      have hv' : (cfc g A) v = 0 := hv
      show (cfc g A) (π g' v) = 0
      have h1 : (cfc g A * π g') v = (π g' * cfc g A) v := by rw [(hcom g g').eq]
      simp only [ContinuousLinearMap.mul_apply] at h1
      rw [h1, hv', map_zero]
    rcases hirr S hSc hSi with hS | hS
    · apply hX
      ext v
      have h1 : (cfc f A) v ∈ S := by
        show (cfc g A) ((cfc f A) v) = 0
        rw [← ContinuousLinearMap.mul_apply, hYX, ContinuousLinearMap.zero_apply]
      rw [hS, Submodule.mem_bot] at h1
      rw [h1, ContinuousLinearMap.zero_apply]
    · apply hY
      ext v
      have h1 : v ∈ S := by rw [hS]; exact Submodule.mem_top
      exact h1
  obtain ⟨r, hr⟩ : (spectrum ℝ A).Nonempty := by
    first
    | exact CFC.spectrum_nonempty ℝ A hA
    | exact hA.spectrum_nonempty
  refine ⟨r, ?_⟩
  have heq : Set.EqOn (fun x : ℝ => x) (fun _ => r) (spectrum ℝ A) := by
    intro x hx
    rcases lt_trichotomy x r with h | h | h
    · exact (hsub x hx r hr h).elim
    · exact h
    · exact (hsub r hr x hx h).elim
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A).symm
    _ = cfc (fun _ : ℝ => r) A := cfc_congr heq
    _ = algebraMap ℝ (H →L[ℂ] H) r := cfc_const r A

end Schur

theorem stSchur : StSchur := by
  intro G H iG iH iI iC π hπ hirr T hT
  have hc : ∀ g, Commute T (π g) := fun g => by
    first
    | exact hT g
    | simpa [Commute, SemiconjBy, ContinuousLinearMap.mul_def] using hT g
  have hcs : ∀ g, Commute (star T) (π g) := fun g => commute_star π hπ T hc g
  obtain ⟨r1, h1⟩ := sa_scalar π hirr (ℜ T : H →L[ℂ] H) (ℜ T).2 (fun g => by
    rw [realPart_apply_coe]
    exact ((hc g).add_left (hcs g)).smul_left _)
  obtain ⟨r2, h2⟩ := sa_scalar π hirr (ℑ T : H →L[ℂ] H) (ℑ T).2 (fun g => by
    rw [imaginaryPart_apply_coe]
    exact (((hc g).sub_left (hcs g)).smul_left _).smul_left _)
  refine ⟨(r1 : ℂ) + Complex.I * r2, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h1, h2]
  ext v
  simp [Algebra.algebraMap_eq_smul_one, add_smul, mul_smul]

end PIW.HCFdeg
