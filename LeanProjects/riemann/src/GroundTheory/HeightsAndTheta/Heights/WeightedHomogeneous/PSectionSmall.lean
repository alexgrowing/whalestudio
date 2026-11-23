import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionSmall

theorem mkF_den_ne_zero {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a) :
    P.mkF s.den ≠ 0 := fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)

theorem den_mul_sub_mem {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q : MvPolynomial (Coord n) ℤ} (h : P.mkF p = s.toFun * P.mkF q) :
    s.den * p - s.num * q ∈ P.ideal := by
  have hG := mkF_den_ne_zero s
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h, IntegralSection.toFun]
  field_simp
  ring

theorem mkF_eq_of_mem {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {e m : MvPolynomial (Coord n) ℤ} (h : s.den * e - s.num * m ∈ P.ideal) :
    P.mkF e = s.toFun * P.mkF m := by
  have hG := mkF_den_ne_zero s
  have h' := (P.mkF_eq_zero_iff _).mpr h
  rw [map_sub, map_mul, map_mul] at h'
  rw [IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hG]
  linear_combination h'

omit [Fintype ι] in

theorem live_of_ne {P : ArithVariety n} {F : Type*} [CommRing F] {z : Cone n F} (hz : z ∈ P.points F)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)

omit [Fintype ι] in

theorem exists_chart {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
  have h : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c hc using h
  exact ⟨c, hc⟩

omit [DecidableEq ι] in

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem eval_cross {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q e m : MvPolynomial (Coord n) ℤ} (hpq : s.den * p - s.num * q ∈ P.ideal)
    (hem : s.den * e - s.num * m ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z q = evalCone z p * evalCone z m := by
  have hmul : s.den * (e * q - p * m) ∈ P.ideal := by
    have h := P.ideal.sub_mem (P.ideal.mul_mem_right q hem) (P.ideal.mul_mem_right m hpq)
    convert h using 1
    ring
  have hmem : e * q - p * m ∈ P.ideal :=
    (P.isPrime.mem_or_mem hmul).resolve_left s.den_not_mem
  have h0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul] at h0 ⊢
  exact sub_eq_zero.mp h0

theorem proof : SectionSmall.Statement := by
  intro ι _ _ n P A s
  have bound : ∀ C : ℝ, s.SupNormLE A C → ∀ p q : MvPolynomial (Coord n) ℤ,
      P.mkF p = s.toFun * P.mkF q →
      ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ Real.exp C * (‖evalCone z q‖ * A.metric z) := by
    intro C hC p q hpq z hz
    obtain ⟨c, hc⟩ := exists_chart hz
    obtain ⟨d, e, he⟩ := s.regular c (live_of_ne hz hc)
    have hcross := eval_cross s (den_mul_sub_mem s hpq) he.2 hz
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hb := hC z hz c d e he hc
    rw [div_le_iff₀ (mul_pos hm hh)] at hb
    have hnorm : ‖evalCone z e‖ * ‖evalCone z q‖ =
        ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖ := by
      rw [← norm_mul, ← norm_mul, hcross]
    refine le_of_mul_le_mul_right ?_ hm
    calc ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖
        = ‖evalCone z e‖ * ‖evalCone z q‖ := hnorm.symm
      _ ≤ Real.exp C * (‖evalCone z (chartMonomial c d)‖ * A.metric z) * ‖evalCone z q‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = Real.exp C * (‖evalCone z q‖ * A.metric z) * ‖evalCone z (chartMonomial c d)‖ := by ring
  refine ⟨bound, ⟨fun hs p q δp δq _ _ _ hpq z hz ↦ ?_, fun hsm z hz c d e he hc ↦ ?_⟩⟩
  · simpa [Real.exp_zero] using bound 0 hs p q hpq z hz
  · obtain ⟨⟨δ, hδ, hδd⟩, hmem⟩ := he
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hsmall := hsm e (chartMonomial c d) δ d hδ (isWeightedHomogeneous_chartMonomial c d)
      (fun k ↦ by rw [hδd k]; ring) (mkF_eq_of_mem s hmem) z hz
    rw [Real.exp_zero, div_le_one (mul_pos hm hh)]
    exact hsmall

end SectionSmall

end

end GroundTheory.Heights₂.Heights
