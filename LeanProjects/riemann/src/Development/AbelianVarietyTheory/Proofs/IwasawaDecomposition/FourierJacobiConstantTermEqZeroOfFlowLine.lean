import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.CuspLimit

open Classical in

theorem tendsto_dirichlet {ι : Type*} (A : ι → ℂ) (a : ι → ℝ) (F : ℝ → ℂ) (T : ℝ)
    (ha : ∀ i, A i ≠ 0 → 0 ≤ a i)
    (hs : ∀ t, T < t → HasSum (fun i => A i * (Real.exp (-(a i * t)) : ℂ)) (F t)) :
    Tendsto F atTop (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
  have h0 : Summable fun i => ‖A i * (Real.exp (-(a i * (T + 1))) : ℂ)‖ :=
    (hs (T + 1) (by linarith)).summable.norm
  have hlim : Tendsto (fun t : ℝ => ∑' i, A i * (Real.exp (-(a i * t)) : ℂ)) atTop
      (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence h0 (fun i => ?_) ?_
    · by_cases hi : A i = 0
      · simp [hi]
      by_cases hz : a i = 0
      · simp [hz]
      have hp : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hz)
      rw [if_neg hz]
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(a i * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul (A i)
      simpa using h2
    · filter_upwards [eventually_ge_atTop (T + 1)] with t ht i
      by_cases hi : A i = 0
      · simp [hi]
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      exact neg_le_neg (mul_le_mul_of_nonneg_left ht (ha i hi))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  exact (hs t ht).tsum_eq

theorem fj_zero_eq_zero_of_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  intro E _ _ _ r X la P ξ x s d T g hP hnn hξ hx hd hg hw
  classical
  have hpi := Real.pi_pos
  set F : ℝ → ℂ := fun t => P (X.flow ξ (fun τ => s τ + (I * t) * (d τ : ℂ)) x) with hF
  have him : ∀ t : ℝ, T < t → T < (I * (t : ℂ)).im := fun t ht => by simpa using ht
  have h1 := tendsto_dirichlet g (fun m : ℤ => 2 * Real.pi * m) F T
    (fun m hm => by
      have : 0 < m := by
        by_contra h
        exact hm (hg m (not_lt.mp h))
      positivity)
    (fun t ht => by
      have h := (hw _ (him t ht)).2
      convert h using 3 with m
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi, ← Complex.exp_int_mul]
      push_cast
      congr 1
      linear_combination (-(2 * (Real.pi : ℂ) * m * t)) * Complex.I_mul_I)
  have e1 : (∑' m : ℤ, if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = 0 := by
    have : (fun m : ℤ => if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = fun _ => 0 := by
      funext m
      split_ifs with h
      · have hm : m = 0 := by simpa [hpi.ne'] using h
        exact hg m hm.le
      · rfl
    rw [this, tsum_zero]
  have h2 := tendsto_dirichlet
    (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
    (fun ν => 4 * Real.pi * ∑ τ, ν τ * d τ) F T
    (fun ν hν => by
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hν)
      have : 0 ≤ ∑ τ, ν τ * d τ := Finset.sum_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le
      positivity)
    (fun t ht => by
      have h := m3bExp_holds r X la P hP ξ hξ x hx _ (hw _ (him t ht)).1
      convert h using 2 with ν
      rw [mul_assoc]
      congr 1
      push_cast
      rw [← Complex.exp_add]
      congr 1
      have e : ∑ τ, (ν τ : ℂ) * (s τ + I * t * (d τ : ℂ)) =
          ∑ τ, (ν τ : ℂ) * s τ + I * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by ring
      rw [e]
      linear_combination (-(4 * (Real.pi : ℂ) * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ))) * Complex.I_mul_I)
  rw [tsum_eq_single (0 : X.Ψ → ℝ) (fun ν hν => by
    split_ifs with h
    · by_contra hne
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hne)
      have hz : ∑ τ, ν τ * d τ = 0 := by simpa [hpi.ne'] using h
      refine hν (funext fun τ => ?_)
      have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le).mp hz τ
        (Finset.mem_univ τ)
      exact (mul_eq_zero.mp this).resolve_right (hd τ).ne'
    · rfl)] at h2
  rw [e1] at h1
  simpa using tendsto_nhds_unique h2 h1

end GlobalTheory.CuspLimit
