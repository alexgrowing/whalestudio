import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LeviTwistLower

theorem main : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  intro n M _ _ _ _ _ z φ ψ δ κ hz hφ hψ hψ0 hδ hκ hκ' hL
  obtain ⟨hκd, hκ1⟩ := contDiff_infty_iff_deriv.1 hκ
  have hκdd : Differentiable ℝ (deriv κ) := (contDiff_infty_iff_deriv.1 hκ1).1
  set k : ℝ → ℝ := fun t => κ (δ * t) with hkdef
  have hk : ContDiff ℝ ∞ k := hκ.comp (contDiff_const.mul contDiff_id)
  have hD : ∀ t, HasDerivAt k (deriv κ (δ * t) * δ) t := by
    intro t
    have h := (hκd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)
    simpa [hkdef, Function.comp_def] using h
  have hDk : deriv k = fun t => deriv κ (δ * t) * δ := funext fun t => (hD t).deriv
  have hDD : ∀ t, deriv (deriv k) t = deriv (deriv κ) (δ * t) * δ ^ 2 := by
    intro t
    rw [hDk]
    have h := ((hκdd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)).mul_const δ
    exact h.deriv.trans (by ring)
  have hks : SmoothR n z (fun x => κ (δ * ψ x)) := SmoothR.comp n z k hk ψ hψ
  refine ⟨hks, fun x ξ => ⟨?_, ?_⟩⟩
  · unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := db_comp_real n z k hk ψ (SmoothR.ckR n z 1 _ hψ) j x
    rw [(hD (ψ x)).deriv] at this
    change db n z j (fun y => ((k (ψ y) : ℝ) : ℂ)) x * _ = _
    rw [this]; ring
  · have hC := chain n M z hz k ψ (contDiff_infty.1 hk 2) hψ x ξ
    rw [(hD (ψ x)).deriv, hDD (ψ x)] at hC
    have hnorm : ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ = ‖dDot n z (fun y => (ψ y : ℂ)) x ξ‖ := by
      have : dbarDot n z (fun y => (ψ y : ℂ)) x ξ = (starRingEnd ℂ) (dDot n z (fun y => (ψ y : ℂ)) x ξ) := by
        unfold dbarDot dDot
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [db_ofReal n z ψ j x, map_mul]
      rw [this, Complex.norm_conj]
    have hsum : Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ =
        Levi n z φ x ξ + Levi n z ψ x ξ + Levi n z (fun y => k (ψ y)) x ξ := by
      rw [levi_add n z (fun y => φ y + ψ y) (fun y => κ (δ * ψ y))
        (SmoothR.ckR n z 2 _ (SmoothR.add n z _ _ hφ hψ)) (SmoothR.ckR n z 2 _ hks) x ξ,
        levi_add n z φ ψ (SmoothR.ckR n z 2 _ hφ) (SmoothR.ckR n z 2 _ hψ) x ξ]
    set α : ℝ := 1 + δ * deriv κ (δ * ψ x) with hα
    have hmem : α ∈ Set.Icc (1 : ℝ) (1 + δ) := by
      obtain ⟨h0, h1⟩ := hκ' (δ * ψ x) (mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x))
      constructor
      · nlinarith
      · nlinarith
    have hnn := hL α hmem x ξ
    rw [levi_add n z φ (fun y => α * ψ y) (SmoothR.ckR n z 2 _ hφ)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z α) hψ)) x ξ,
      levi_const_mul n z α ψ (SmoothR.ckR n z 2 _ hψ) x ξ] at hnn
    rw [hsum, hC, hnorm]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hnn ⊢
    rw [hα] at hnn
    nlinarith

end GlobalTheory.LeviTwistLower
