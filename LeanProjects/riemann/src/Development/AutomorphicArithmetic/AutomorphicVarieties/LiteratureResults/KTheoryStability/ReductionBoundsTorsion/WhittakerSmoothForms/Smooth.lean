import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SkipSuccAbove

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem eta_zero {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (σ : ℕ → Γ) :
    eta A φ c 0 σ = fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := rfl

theorem eta_succ {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ) :
    eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) := rfl

theorem psi_contDiffAt (H : Hyp U A φ) (γ : Γ) {h : V} (hh : h ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psi A φ γ) h := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) φ (A γ⁻¹ h) :=
    H.smooth.contDiffAt (H.isOpen.mem_nhds (H.mapsTo _ h hh))
  exact h1.comp h (A γ⁻¹).contDiff.contDiffAt

theorem Kf_contDiffOn (hL : PLoc U A φ) (H : Hyp U A φ) {q : ℕ}
    (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (hβ : ∀ τ, ContDiffOn ℝ (⊤ : ℕ∞) (β τ) U) (σ : ℕ → Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Kf A φ β σ) U := by
  intro h hh
  obtain ⟨s, W, hW, hWU, hz⟩ := hL H h hh
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ∑ γ ∈ s, psi A φ γ x • β (cons γ σ) x) h := by
    apply ContDiffAt.sum
    intro γ _
    exact (psi_contDiffAt U A φ H γ hh).smul ((hβ _).contDiffAt (H.isOpen.mem_nhds hh))
  refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW] with x hx
  show (∑ᶠ γ, psi A φ γ x • β (cons γ σ) x) = _
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  by_contra hn
  apply hγ
  simp [hz γ hn x hx]

theorem extDeriv_contDiffOn (H : Hyp U A φ) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ (⊤ : ℕ∞) ω U) : ContDiffOn ℝ (⊤ : ℕ∞) (extDeriv ω) U := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ ω) U := hω.fderiv_of_isOpen H.isOpen (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn hd

theorem pSmooth (hL : PLoc U A φ) : PSmooth U A φ := by
  intro H k c j σ
  have key : ∀ (i : ℕ) (τ : ℕ → Γ), ContDiffOn ℝ (⊤ : ℕ∞) (eta A φ c i τ) U := by
    intro i
    induction i with
    | zero =>
      intro τ
      rw [eta_zero]
      exact contDiffOn_const
    | succ i ih =>
      intro τ
      rw [eta_succ]
      exact extDeriv_contDiffOn U A φ H (Kf_contDiffOn U A φ hL H _ ih τ)
  exact ⟨key j σ, Kf_contDiffOn U A φ hL H _ (key j) σ⟩

theorem pClosed (hS : PSmooth U A φ) : PClosed U A φ := by
  intro H k c j σ h hh
  cases j with
  | zero =>
    rw [eta_zero]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  | succ j =>
    rw [eta_succ]
    exact extDeriv_extDeriv_apply ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds hh))
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        first
        | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
        | (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.2 le_top)
        | simp)

theorem pDep : PDep A φ := by
  intro k c j
  induction j with
  | zero =>
    intro σ σ' hσ
    rw [eta_zero, eta_zero]
    have e : (fun i : Fin (k + 2) => σ i) = fun i : Fin (k + 2) => σ' i := by
      funext i
      have := i.isLt
      exact hσ i (by omega)
    rw [e]
  | succ j ih =>
    intro σ σ' hσ
    rw [eta_succ, eta_succ]
    have e : Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
      funext x
      simp only [Kf]
      congr 1
      funext γ
      rw [ih (cons γ σ) (cons γ σ')]
      intro n hn
      cases n with
      | zero => rfl
      | succ m => exact hσ m (by omega)
    rw [e]

end PositivityTheory.KB.WhittakerCocycle

end
