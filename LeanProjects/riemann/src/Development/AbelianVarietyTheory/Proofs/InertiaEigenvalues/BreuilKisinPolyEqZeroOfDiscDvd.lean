import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOnePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDiscStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscRem

theorem norm_add_le_max' (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (x y : Disc l u ρ) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add, norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem norm_toDisc_l_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖toDisc l u ρ (l : A)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  exact (norm_ofPre l u ρ _).trans_le (gauge_le l u ρ (by positivity)
    (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], by simp⟩))

theorem coeff_mul_disc (l : ℕ) {R : Type} [CommRing R] (ρ : ℝ≥0)
    (a : ℕ → (Disc l (X : R⟦X⟧) ρ →+ Disc l (0 : R) 1))
    (h1 : ∀ n x, a n (toDisc l (X : R⟦X⟧) ρ x) = toDisc l (0 : R) 1 (coeff n x))
    (hc : ∀ n, Continuous (a n)) (s : R⟦X⟧) (n : ℕ) (y : Disc l (X : R⟦X⟧) ρ) :
    a n (toDisc l (X : R⟦X⟧) ρ s * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, toDisc l (0 : R) 1 (coeff p.1 s) * a p.2 y := by
  refine (denseRange_ofPre l (X : R⟦X⟧) ρ).induction_on y
    (isClosed_eq ((hc n).comp (continuous_const.mul continuous_id))
      (continuous_finset_sum _ fun p _ => continuous_const.mul (hc p.2))) fun z => ?_
  obtain ⟨k, b, h⟩ := IsLocalization.Away.surj (l : R⟦X⟧) z
  have h' : (l ^ k : ℕ) • ofPre l (X : R⟦X⟧) ρ z = toDisc l (X : R⟦X⟧) ρ b := by
    have := congrArg (ofPre l (X : R⟦X⟧) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [nsmul_eq_mul, Nat.cast_pow, mul_comm]
    exact this
  refine ((isUnit_l_disc l (0 : R) 1).pow k).mul_left_cancel ?_
  rw [← Nat.cast_pow, ← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← mul_smul_comm, h', ← map_mul, h1,
    coeff_mul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← mul_smul_comm, ← map_nsmul, h', h1, map_mul]

theorem rho_zero {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) :
    0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
  have he : (0 : ℝ) < bk.Ep.natDegree := Nat.cast_pos.2 bk.deg_pos
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith), ?_⟩
  rw [BK.ρ₀, NNReal.coe_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), neg_mul,
    one_div_mul_cancel he.ne', Real.rpow_neg_one, NNReal.coe_natCast]

theorem eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (r : Polynomial (Wq l bk.a)),
    r.degree < bk.Ep.degree →
    toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) → r = 0 := by
  intro l hl K bk r hr ⟨y, hy⟩
  obtain ⟨h0, h1, hpow⟩ := rho_zero bk
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk bk.ρ₀ h0 h1
  obtain ⟨-, -, hinj, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have h1' : (bk.ρ₀ : ℝ) < 1 := h1
  have hc : ∀ n, Continuous (a n) := fun n =>
    AddMonoidHomClass.continuous_of_bound _ ((bk.ρ₀ : ℝ) ^ n)⁻¹ fun z => by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact ha2 n z
  have hy0 : y = 0 := by
    refine norm_le_zero_iff.1 (ha3 y 0 le_rfl fun m₀ => ?_)
    by_contra hneg
    push Not at hneg
    set c := ‖a m₀ y‖ * (bk.ρ₀ : ℝ) ^ m₀ with hcdef
    have hfin : {n | c ≤ ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n}.Finite := by
      have := (ha4 y).eventually (gt_mem_nhds hneg)
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at this
      simpa only [not_lt] using this
    obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal ⟨m₀, le_refl c⟩
    have hlt : ∀ n, m < n → ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n < c := fun n hn => by
      by_contra h
      exact (hmax (not_lt.1 h) hn.le).not_gt hn
    have key := coeff_mul_disc l bk.ρ₀ a ha1 hc bk.E (bk.Ep.natDegree + m) y
    have hz : coeff (bk.Ep.natDegree + m) (r : bk.S) = 0 := by
      rw [Polynomial.coeff_coe]
      refine Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le ?_)
      rw [Polynomial.degree_eq_natDegree bk.monic.ne_zero]
      exact_mod_cast Nat.le_add_right _ _
    rw [← hy, ha1, hz, map_zero, ← Finset.add_sum_erase _ _
      (show (bk.Ep.natDegree, m) ∈ Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m) by simp)] at key
    have hlead : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [Polynomial.coeff_coe]; exact bk.monic
    simp only [hlead, map_one, one_mul] at key
    have hsum : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m)).erase (bk.Ep.natDegree, m),
        toDisc l (0 : Wq l bk.a) 1 (coeff p.1 bk.E) * a p.2 y‖ * (bk.ρ₀ : ℝ) ^ m < c := by
      refine Finset.sum_induction _ (fun x => ‖x‖ * (bk.ρ₀ : ℝ) ^ m < c) (fun x z hx hz => ?_)
        (by simpa using hneg) fun p hp => ?_
      · refine (mul_le_mul_of_nonneg_right (norm_add_le_max' l _ _ x z) (by positivity)).trans_lt ?_
        rcases max_cases ‖x‖ ‖z‖ with h | h <;> rw [h.1] <;> assumption
      · obtain ⟨i, j⟩ := p
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
        rw [Polynomial.coeff_coe]
        rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
        · obtain ⟨w, hw⟩ := bk.dvd_coeff i h
          have hn : ‖toDisc l (0 : Wq l bk.a) 1 (bk.Ep.coeff i)‖ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := by
            rw [hw, map_mul, hpow]
            exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_l_le l _ _) (norm_toDisc_le _)
              (norm_nonneg _) (by positivity)).trans (mul_one _).le)
          refine lt_of_le_of_lt ?_ (hlt j (by omega))
          have hp2 : (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) ≤ (bk.ρ₀ : ℝ) ^ j :=
            pow_le_pow_of_le_one h0'.le h1'.le (by omega)
          calc _ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree * ‖a j y‖ * (bk.ρ₀ : ℝ) ^ m :=
                mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (by positivity)
            _ = ‖a j y‖ * (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)
        · exact (hp.1 ⟨h, by omega⟩).elim
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
          simpa using hneg
    rw [eq_neg_of_add_eq_zero_right key.symm, norm_neg] at hsum
    exact hsum.not_ge hm
  ext1 n
  apply hinj
  have := ha1 n (r : bk.S)
  rw [hy, hy0, mul_zero, map_zero, Polynomial.coeff_coe] at this
  rw [← this, Polynomial.coeff_zero, map_zero]

end GlobalTheory.BSP.DiscRem
