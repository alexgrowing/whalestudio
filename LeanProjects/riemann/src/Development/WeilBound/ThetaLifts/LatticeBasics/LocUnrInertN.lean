import Development.AutomorphicSpectrum.Proofs.TwistedProofs.UnramDoublingInert

noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open MeasureTheory Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

theorem prod_fold (T : ℕ → ℂ) (n : ℕ) :
    (∏ i : Fin (n / 2), T (n - 1 - i) * T i) * (if Odd n then T (n / 2) else 1) = ∏ k ∈ Finset.range n, T k := by
  rw [Fin.prod_univ_eq_prod_range (fun i => T (n - 1 - i) * T i), Finset.prod_mul_distrib]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_neg (by simp), show 2 * m / 2 = m by omega, two_mul, Finset.prod_range_add, mul_one, mul_comm,
      ← Finset.prod_range_reflect (fun i => T (m + i))]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => congrArg T (by have := Finset.mem_range.1 hi; omega))
  · rw [if_pos (by simp), show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 = m + 1 + m by ring, Finset.prod_range_add,
      Finset.prod_range_succ, ← Finset.prod_range_reflect (fun i => T (m + 1 + i)), mul_assoc, mul_comm]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => congrArg T (by have := Finset.mem_range.1 hi; omega))

theorem triv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv (ϖ : L) σ q) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] (μ : Measure (GU σ n)) [μ.IsHaarMeasure]
    (hμ : μ (KU σ n) = 1) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n 1 s Φ) :
    Integrable (fun g => Φ (io1 σ n g)) μ ∧ (∫ g, Φ (io1 σ n g) ∂μ) *
      ∏ i ∈ Finset.range n, (1 - (-1) ^ (n - (i + 1)) * (q : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹ =
      ∏ i ∈ Finset.range n, (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + n / 2 - i)))⁻¹ := by
  obtain ⟨α, hα, hw⟩ := isZonal_one hU n
  have h2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have lt : ∀ z : ℂ, z.re < 0 → ‖(q : ℂ) ^ z‖ < 1 := fun z hz => by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2) hz
  have y0 : varY q ((1 : Lˣ →* ℂˣ) ϖ) s = (q : ℂ) ^ (-(2 * s + 1)) := by simp [varY]
  have y1 : ∀ i, (q : ℂ) ^ (-(2 * s + 1)) * α i = (q : ℂ) ^ (-(2 * s + 1) + (n - 1 - 2 * (i.val : ℂ))) := fun i => by
    rw [hα, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hq]; push_cast; rfl
  have y2 : ∀ i, (q : ℂ) ^ (-(2 * s + 1)) / α i = (q : ℂ) ^ (-(2 * s + 1) - (n - 1 - 2 * (i.val : ℂ))) := fun i => by
    rw [hα, ← Complex.cpow_intCast, ← Complex.cpow_sub _ _ hq]; push_cast; rfl
  obtain ⟨h3, h4, -⟩ := (GlobalTheory.CompanionTheory.InertZetaTop.unramDoublingInert L ϖ σ q n hU μ hμ 1 (fun _ _ => rfl) s Φ hΦ α _ hw).1 (by
    rw [y0]
    refine ⟨lt _ (by simp; linarith), fun i => ?_⟩
    have h5 : 2 * (i.val : ℝ) + 1 ≤ n := by exact_mod_cast (by have := i.2; omega : 2 * i.val + 1 ≤ n)
    have h6 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    rw [← norm_mul, ← norm_inv, ← norm_mul, ← div_eq_mul_inv, y1, y2]
    exact ⟨lt _ (by simp; linarith), lt _ (by simp; linarith)⟩)
  simp only [mul_one] at h3 h4
  refine ⟨h3, ?_⟩
  have e : ∀ z : ℂ, ((q ^ 2 : ℕ) : ℂ) ^ z = (q : ℂ) ^ (2 * z) := fun z => by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]; rfl
  rw [h4, closedForm, y0, ← prod_fold (fun i => (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + n / 2 - i)))⁻¹), mul_assoc (Finset.prod _ _), mul_right_comm,
    ← Finset.prod_range_reflect, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
  · congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have := i.2
      rw [y1, y2, e, e, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      congr 4 <;> push_cast <;> ring
    · split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [e, show (2 * m + 1) / 2 = m by omega]
        congr 3; push_cast; ring
      · rfl
  · intro i hi
    have hi := Finset.mem_range.1 hi
    have e2 : (-(q : ℂ)) ^ (n - 1 - i) * varX q n ((1 : Lˣ →* ℂˣ) ϖ) s = (-1) ^ (n - (i + 1)) * (q : ℂ) ^ (-(2 * s + (i + 1 : ℕ))) := by
      rw [neg_pow, varX, MonoidHom.one_apply, Units.val_one, one_mul, mul_assoc, ← Complex.cpow_natCast (q : ℂ),
        ← Complex.cpow_add _ _ hq, Nat.cast_sub (by omega), Nat.cast_sub (by omega), show n - 1 - i = n - (i + 1) by omega]
      congr 2; push_cast; ring
    rw [e2]
    refine mul_inv_cancel₀ (sub_ne_zero.2 fun h => ?_)
    have h6 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have := lt (-(2 * s + (i + 1 : ℕ))) (by simp; linarith)
    have h7 := congrArg norm h
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h7
    exact this.ne h7.symm

end GlobalTheory.ThK.Dbl.Inert

end
