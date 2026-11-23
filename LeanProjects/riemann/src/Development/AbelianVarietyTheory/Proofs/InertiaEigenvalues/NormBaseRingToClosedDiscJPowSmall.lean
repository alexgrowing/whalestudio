import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSmall

def ballIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ) : Ideal A :=
  Submodule.comap (Algebra.linearMap A (PreDisc l u ρ)) (ball l u ρ r)

theorem mem_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} {x : A} :
    x ∈ ballIdeal l u ρ r ↔ algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ r := Iff.rfl

theorem ballIdeal_mul_le {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r s : ℝ} (hr : 0 ≤ r) :
    ballIdeal l u ρ r * ballIdeal l u ρ s ≤ ballIdeal l u ρ (r * s) :=
  Ideal.mul_le.2 fun x hx y hy => by
    rw [mem_ballIdeal, map_mul]
    exact mul_mem_ball l u ρ hr hx hy

theorem pow_le_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} (hr : 0 ≤ r)
    {I : Ideal A} (hI : I ≤ ballIdeal l u ρ r) : ∀ n : ℕ, I ^ n ≤ ballIdeal l u ρ (r ^ n)
  | 0 => by
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    refine (Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one).ge
    rw [mem_ballIdeal, map_one]
    exact Submodule.subset_span ⟨0, 0, 0, by simp, by simp⟩
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono (pow_le_ballIdeal hr hI n) hI).trans (ballIdeal_mul_le (pow_nonneg hr n))

theorem exists_E_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · rw [h, if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hd
  have h2 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  refine ⟨(q : bk.S), ?_⟩
  show ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  nth_rewrite 1 [h2]
  simp [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C]
  left
  exact map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) l

end GlobalTheory.BSP.DiscSmall

open GlobalTheory.BSP.DiscSmall in

theorem GlobalTheory.BSP.norm_toDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s,
    ‖toDisc l (s X) ρ x‖ ≤ r := by
  intro l hl K bk A _ s ρ hρ0 hρ1 r hr
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  set t : ℝ := max (1 / (l : ℝ)) ((ρ : ℝ) ^ bk.Ep.natDegree) with ht
  have ht0 : 0 < t := lt_max_of_lt_left (one_div_pos.2 hl0)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have ht1 : t < 1 := max_lt ((div_lt_one hl0).2 hl1) (pow_lt_one₀ ρ.2 hρ1' bk.deg_pos.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr ht1
  have hlmem : algebraMap A (PreDisc l (s X) ρ) (l : A) ∈ ball l (s X) ρ t := by
    refine Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩
    have : 1 / (l : ℝ) * l ≤ t * l := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0.le
    rw [one_div_mul_cancel hl0.ne'] at this
    simpa using this
  have hJ : bk.J.map s ≤ ballIdeal l (s X) ρ t := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, sup_le_iff,
      Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff, Set.singleton_subset_iff]
    constructor
    · show s (l : bk.S) ∈ ballIdeal l (s X) ρ t
      rw [map_natCast, mem_ballIdeal]
      exact hlmem
    · show s bk.E ∈ ballIdeal l (s X) ρ t
      obtain ⟨q, hq⟩ := exists_E_eq bk
      rw [hq, map_add, map_mul, map_pow, map_natCast, mem_ballIdeal, map_add, map_mul, mul_comm, ← Algebra.smul_def]
      refine add_mem (Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, by simp⟩) (Submodule.smul_mem _ _ hlmem)
      show (l:ℝ)^0 * (ρ:ℝ)^bk.Ep.natDegree ≤ t * (l:ℝ)^0
      simp only [pow_zero, one_mul, mul_one]
      exact le_max_right _ _
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have hx' := pow_le_ballIdeal ht0.le hJ n hx
  rw [toDisc, RingHom.comp_apply, norm_ofPre]
  exact (gauge_le l (s X) ρ (pow_pos ht0 n) hx').trans hn.le
