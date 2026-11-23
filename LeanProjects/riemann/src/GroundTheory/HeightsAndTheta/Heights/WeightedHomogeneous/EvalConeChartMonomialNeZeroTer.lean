import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartVanishing

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def evalHom {F : Type*} [CommRing F] (z : Cone n F) : MvPolynomial (Coord n) ℤ →+* F :=
  eval₂Hom (Int.castRingHom F) fun v : Coord n ↦ z v.1 v.2

omit [Fintype ι] [DecidableEq ι] in
theorem evalHom_apply {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalHom z f = evalCone z f := rfl

omit [Fintype ι] in

theorem mkF_X_ne_zero (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 :=
  fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

theorem chartMonomial_mem_of_not_live (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  simp only [ArithVariety.IsLive, not_forall, not_not] at hc
  obtain ⟨k, hk⟩ := hc
  rw [chartMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hk _ (hd k))

theorem exists_clear_denom (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have hne := mkF_X_ne_zero P hc v.1
    simp only [ArithVariety.chartCoord, chartMonomial, Pi.one_apply, pow_one, map_prod, map_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.1)]
    field_simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * chartMonomial c 1 ^ e' + f' * chartMonomial c 1 ^ e, ?_⟩
    simp only [map_add, map_mul, map_pow, ← hf, ← hf']
    ring
  | neg x _ hx =>
    obtain ⟨e, f, hf⟩ := hx
    refine ⟨e, -f, ?_⟩
    rw [map_neg, ← hf]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * f', ?_⟩
    rw [map_mul, ← hf, ← hf']
    ring

theorem exists_common_denom (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {m : ℕ} {u : Fin m → P.FunField} (hu : ∀ j, u j ∈ P.chartRing c) :
    ∃ (E : ℕ) (f : Fin m → MvPolynomial (Coord n) ℤ),
      ∀ j, u j * P.mkF (chartMonomial c 1) ^ E = P.mkF (f j) := by
  choose e f hf using fun j ↦ exists_clear_denom P hc (hu j)
  refine ⟨∑ j, e j, fun j ↦ f j * chartMonomial c 1 ^ (∑ i, e i - e j), fun j ↦ ?_⟩
  have hle : e j ≤ ∑ i, e i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (e i)) (Finset.mem_univ j)
  rw [map_mul, map_pow, ← hf j, ← Nat.add_sub_cancel' hle, pow_add, Nat.add_sub_cancel_left]
  ring

theorem cross_mem_of_live {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {c c' : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (hc' : P.IsLive c')
    (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
  ring

theorem mkF_chartMonomial_mul_chartPow {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ (d k + D.deg k).toNat) := by
  simp only [chartMonomial, ArithVariety.chartPow, map_prod, map_pow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (mkF_X_ne_zero P hc k),
    Int.toNat_of_nonneg (hd k)]

omit [DecidableEq ι] in

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hz : ∀ k, z k (c k) ≠ 0) (e : ι → ℕ) : evalCone z (chartMonomial c e) ≠ 0 := by
  rw [evalCone_chartMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hz k)

theorem exists_ne_zero_of_live {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) ≠ 0) : ∃ j, evalCone z (g c j) ≠ 0 := by
  by_contra h0
  simp only [not_exists, not_not] at h0
  have hzc : ∀ k, z k (c k) ≠ 0 := by
    rw [evalCone_chartMonomial] at hm
    intro k
    have hk := Finset.prod_ne_zero_iff.mp hm k (Finset.mem_univ k)
    exact (pow_ne_zero_iff (by have := hg.pos k; omega)).mp hk
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  obtain ⟨E, f, hf⟩ := exists_common_denom P hc hu
  have hcp : P.chartPow c D.deg ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero P hc k)
  have hsum' : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    rw [← one_mul (P.chartPow c D.deg), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  set Q := chartMonomial c fun k ↦ (d k + D.deg k).toNat
  have hmem : ∑ j, f j * g c j - chartMonomial c 1 ^ E * Q ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_sum, map_mul, map_pow,
      ← mkF_chartMonomial_mul_chartPow D hg.nonneg hc, ← hsum', sub_eq_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, ← hf j, hg.value c hc j]
    ring
  have hv := hz.2 _ hmem
  rw [← evalHom_apply, map_sub, map_sum, map_mul, map_pow] at hv
  simp only [map_mul, evalHom_apply, h0, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero] at hv
  exact mul_ne_zero (pow_ne_zero _ (evalCone_chartMonomial_ne_zero hzc 1))
    (evalCone_chartMonomial_ne_zero hzc _) hv

theorem eq_zero_of_live {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) = 0) (j : Fin (D.size + 1)) :
    evalCone z (g c j) = 0 := by
  have hex : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c' hc'z using hex
  have hlive : P.IsLive c' := fun k hk ↦ hc'z k (by
    have := hz.2 _ hk
    simpa [evalCone] using this)
  have hv := hz.2 _ (cross_mem_of_live hg hc hlive j)
  rw [← evalHom_apply, map_sub, map_mul, map_mul, evalHom_apply, evalHom_apply, evalHom_apply,
    evalHom_apply, hm, zero_mul, sub_zero] at hv
  exact (mul_eq_zero.mp hv).resolve_left (evalCone_chartMonomial_ne_zero hc'z d)

theorem proof : ChartVanishing.Statement := by
  intro ι _ _ n P D d g hg z hz c
  by_cases hc : P.IsLive c
  · constructor
    · intro h0
      by_contra hm
      obtain ⟨j, hj⟩ := exists_ne_zero_of_live hg hz hc hm
      exact hj (h0 j)
    · exact eq_zero_of_live hg hz hc
  · refine ⟨fun _ ↦ hz.2 _ (chartMonomial_mem_of_not_live P hc hg.pos), fun _ j ↦ ?_⟩
    rw [hg.dead c hc j, ← evalHom_apply, map_zero]

end ChartVanishing

end

end GroundTheory.Heights₂.Heights
