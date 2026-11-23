import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModelNefness

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ProperFromMinimum

theorem bound_of_ineqs {K K' c i δ S n p : ℝ} {a : ℕ} (hδ : 0 < δ) (hac : (a : ℝ) * c < i)
    (hS : 0 ≤ S) (h1 : Real.exp (-(2 * c * p)) ≤ K * S) (h2 : n ≤ K' * Real.exp (-(2 * i * p)))
    (h3 : δ * S ^ a ≤ n) : p ≤ K ^ a * K' / δ / (2 * (i - a * c)) := by
  have hK : 0 ≤ K := by
    by_contra hK
    have : K * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hK)) hS
    linarith [Real.exp_pos (-(2 * c * p))]
  have hKa : 0 ≤ K ^ a := pow_nonneg hK a
  have e1 : Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * S ^ a := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 a
  have e2 : δ * Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * K' * Real.exp (-(2 * i * p)) := by
    calc δ * Real.exp (-(2 * c * p)) ^ a ≤ δ * (K ^ a * S ^ a) :=
          mul_le_mul_of_nonneg_left e1 hδ.le
      _ = K ^ a * (δ * S ^ a) := by ring
      _ ≤ K ^ a * (K' * Real.exp (-(2 * i * p))) := mul_le_mul_of_nonneg_left (h3.trans h2) hKa
      _ = _ := by ring
  have e3 : Real.exp (-(2 * c * p)) ^ a =
      Real.exp (2 * (i - a * c) * p) * Real.exp (-(2 * i * p)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [e3, ← mul_assoc] at e2
  have e4 : δ * Real.exp (2 * (i - a * c) * p) ≤ K ^ a * K' :=
    le_of_mul_le_mul_right e2 (Real.exp_pos _)
  have e5 : 2 * (i - a * c) * p ≤ Real.exp (2 * (i - a * c) * p) := by
    linarith [Real.add_one_le_exp (2 * (i - a * c) * p)]
  have hd : 0 < 2 * (i - a * c) := by linarith
  rw [le_div_iff₀ hd, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_left e5 hδ.le]

theorem exists_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (L eW : Wt X.Ψ r) (N a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ), (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x) → InterpolationModelInequalities X L eW w et c i ph → (a : ℝ) * c < i → ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by
  intro E _ _ _ r X L eW N a w et c i ph hph hI hac δ hδ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hsub : Subsingleton (Frame X.Ψ 0) := inferInstance
    refine ⟨X.dom, (Set.subsingleton_of_subsingleton).finite.isCompact, subset_rfl, ?_⟩
    intro x hx _
    refine ⟨1, X.Γ.one_mem, x, fun τ => ⟨(hx τ).1, fun a => a.elim0⟩, ?_⟩
    rwa [Subsingleton.elim (lact 1 (rmul x x)) x]
  obtain ⟨ca, ε0, hca, hε0, hlow⟩ := hph
  obtain ⟨⟨K, hK⟩, K', hK'⟩ := hI
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max (K ^ a * K' / δ / (2 * (i - a * c))) 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hε : 0 < min ε0 (Real.sqrt (ca / B)) := lt_min hε0 (Real.sqrt_pos.2 (div_pos hca hB0))
  obtain ⟨C, hC, hCd, hmeet⟩ := reductionTheory_holds (E := E) r X _ hε
  refine ⟨C, hC, hCd, fun x hx h3 => hmeet x hx ?_⟩
  by_cases hsmall : X.la1 x < ε0
  · refine (min_le_right _ _).trans ?_
    have hpos : 0 < X.la1 x := la1_pos_of_mem_dom X hr hx
    have hp : ph x ≤ B := by
      rw [hB]
      exact (bound_of_ineqs hδ hac (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hK x hx) (hK' x hx)
        h3).trans (le_max_left _ _)
    have h4 : ca / X.la1 x ^ 2 ≤ B := (hlow x hx hsmall).trans hp
    rw [div_le_iff₀ (by positivity)] at h4
    apply Real.sqrt_le_iff.2
    refine ⟨hpos.le, ?_⟩
    rw [div_le_iff₀ hB0]
    linarith
  · exact (min_le_left _ _).trans (not_lt.1 hsmall)

end GlobalTheory.ProperFromMinimum
