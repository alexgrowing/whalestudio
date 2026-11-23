import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
open FunctorialResolution.Blowup

namespace UpperTheory.ChartGen

variable {R : Type} [CommRing R]

private theorem val_rho (I : Ideal R) (c : ↥I) (r : R) :
    HomogeneousLocalization.val (chartRingHom I c r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(Submonoid.powers (reesGenerator I c))) := rfl

private theorem cancel_rho (I : Ideal R) (c : ↥I) (n : ℕ)
    {x y : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)}
    (h : x * chartRingHom I c (c : R) ^ n = y * chartRingHom I c (c : R) ^ n) : x = y := by
  have hn := pow_mem (chartRingHom_mem_nonZeroDivisors I c) n
  have h0 : (x - y) * chartRingHom I c (c : R) ^ n = 0 := by rw [sub_mul, h, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hn).2 _ h0)

private theorem exists_mul_pow_eq (I : Ideal R) (c : ↥I)
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * chartRingHom I c (c : R) ^ n = chartRingHom I c r := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesGrading I)
    (reesGenerator_mem_reesGrading I c) z
  have hx' : x ∈ reesGrading I n := by simpa using hx
  obtain ⟨r, hr, hxr⟩ := (mem_reesGrading_iff_monomial I n x).1 hx'
  refine ⟨n, r, hr, ?_⟩
  rw [← map_pow, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    val_rho, val_rho, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hpow : ((reesGenerator I c ^ n : ↥(reesAlgebra I)) : Polynomial R) =
      Polynomial.monomial n ((c : R) ^ n) := by
    rw [SubmonoidClass.coe_pow, reesGenerator_coe, Polynomial.monomial_pow, one_mul]
  push_cast [reesDegreeZeroEquiv_coe_coe, hxr, hpow]
  simp [Polynomial.C_mul_monomial, Polynomial.monomial_mul_C, mul_comm]
  rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]

end UpperTheory.ChartGen

open UpperTheory.ChartGen in
theorem UpperTheory.surjective_eval_blowupChart_of_span_eq :
    ∀ {R : Type} [CommRing R] (I : Ideal R) {M : ℕ} (a : Fin (M + 1) → ↥I), Ideal.span (Set.range fun l => (a l : R)) = I → ∀ m : Fin (M + 1), Function.Surjective (MvPolynomial.eval₂Hom (chartRingHom I (a m)) (fun l => chartFraction I (a m) (a l))) := by
  intro R _ I M a hspan m
  set c := a m with hc
  set φ := MvPolynomial.eval₂Hom (chartRingHom I c) (fun l => chartFraction I c (a l)) with hφ
  have hC : ∀ r : R, chartRingHom I c r ∈ φ.range := fun r =>
    ⟨MvPolynomial.C r, by simp [hφ]⟩
  have hX : ∀ l, chartFraction I c (a l) ∈ φ.range := fun l =>
    ⟨MvPolynomial.X l, by simp [hφ]⟩
  have hfrac : ∀ b : ↥I, chartFraction I c b ∈ φ.range := by
    intro b
    have hb : (b : R) ∈ Ideal.span (Set.range fun l => (a l : R)) := by rw [hspan]; exact b.2
    obtain ⟨s, hs⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hb
    have hw : ∑ l, chartRingHom I c (s l) * chartFraction I c (a l) ∈ φ.range :=
      sum_mem fun l _ => mul_mem (hC _) (hX l)
    have heq : chartFraction I c b = ∑ l, chartRingHom I c (s l) * chartFraction I c (a l) := by
      apply cancel_rho I c 1
      rw [pow_one, ← chartRingHom_coe_eq_chartFraction_mul, ← hs, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, chartRingHom_coe_eq_chartFraction_mul I c (a l), mul_assoc]
    rw [heq]
    exact hw
  have hpow : ∀ (n : ℕ), ∀ r ∈ I ^ n, ∃ w ∈ φ.range,
      chartRingHom I c r = w * chartRingHom I c (c : R) ^ n := by
    intro n
    induction n with
    | zero => exact fun r _ => ⟨_, hC r, by simp⟩
    | succ n ih =>
      intro r hr
      rw [pow_succ] at hr
      refine Submodule.mul_induction_on hr ?_ ?_
      · intro s hs b hb
        obtain ⟨w, hw, hwe⟩ := ih s hs
        refine ⟨w * chartFraction I c ⟨b, hb⟩, mul_mem hw (hfrac _), ?_⟩
        have hbe := chartRingHom_coe_eq_chartFraction_mul I c ⟨b, hb⟩
        rw [map_mul, hwe]
        simp only at hbe
        rw [hbe]
        ring
      · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
        exact ⟨wx + wy, add_mem hwx hwy, by rw [map_add, hx, hy, add_mul]⟩
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_mul_pow_eq I c z
  obtain ⟨w, hw, hwe⟩ := hpow n r hr
  have hzw : z = w := cancel_rho I c n (hz.trans hwe)
  rw [hzw]
  exact hw
