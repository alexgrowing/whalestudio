import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound

namespace GlobalTheory.FlatChecks

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem one_le_tt_iff (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    1 ≤ X.tt ξ x τ ↔ 0 < X.c τ * X.maj x τ (Data.emb τ.1 ξ) ∧ X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1 := by
  unfold Data.tt
  generalize X.c τ * X.maj x τ (Data.emb τ.1 ξ) = h
  constructor
  · intro h1
    have hp : 0 < h := by
      by_contra hn
      have : 1 / h ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one (not_lt.1 hn)
      linarith
    exact ⟨hp, by rwa [le_div_iff₀ hp, one_mul] at h1⟩
  · rintro ⟨hp, h1⟩
    rwa [le_div_iff₀ hp, one_mul]

theorem cfwM_all_eta (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 ≤ a)
    (η : ℝ) (hη : 0 < η) : ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by
  by_cases h2 : η < 1 / 2
  · exact h.2 η hη h2
  · obtain ⟨C, A', hC⟩ := h.1
    refine ⟨C, A', fun x hx ξ _ ht => ?_⟩
    have h0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => zero_le_one.trans (ht τ)
    have h1 : 0 ≤ 8 * Real.pi * (2 * η - 1) * a * ⨅ τ, X.tt ξ x τ := by
      have := Real.pi_pos
      have : 0 ≤ 2 * η - 1 := by linarith
      positivity
    have := hC x hx
    nlinarith

theorem sum_le_of_mem_multiLt {n a0 T : ℕ} (h : a0 ≤ T + 1) {α : Fin n → ℕ}
    (hα : α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt n a0) : (∑ q, α q) + (T - ∑ q, α q) = T := by
  simp only [ReciprocityTheory.ChartRestriction.G.AR.multiLt, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple] at hα
  obtain ⟨d, hd, hs⟩ := hα
  omega

theorem coord_differentiableAt (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (j : Fin Fl.δ) :
    DifferentiableAt ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) 0 := by
  by_contra hn
  have h := Fl.coord j
  rw [fderiv_zero_of_not_differentiableAt hn] at h
  apply h
  have h2 := Xa.n_ge
  haveI : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have b := (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_zero]
  exact LinearMap.det_zero' b

theorem exists_s_ne_of_empty (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (h : Fl.δ = 0) :
    ∀ x ∈ X.dom, ∃ k, Fl.s k x ≠ 0 := by
  intro x hx
  by_contra hn
  push Not at hn
  obtain ⟨j, -⟩ := (Fl.S_eq x hx).1 hn
  exact absurd j.2 (by omega)

end GlobalTheory.FlatChecks
