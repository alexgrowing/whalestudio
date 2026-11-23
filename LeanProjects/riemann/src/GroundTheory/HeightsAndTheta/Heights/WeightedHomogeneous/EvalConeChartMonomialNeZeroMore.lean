import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionInjectivity

set_option linter.unusedSectionVars false

theorem isLive_of_mem_points {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem chartForm_cross {P : ArithVariety n} {num den : MvPolynomial (Coord n) ℤ}
    (hden : den ∉ P.ideal) {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ}
    {f f' : MvPolynomial (Coord n) ℤ} (h : den * f - num * chartMonomial c d ∈ P.ideal)
    (h' : den * f' - num * chartMonomial c d' ∈ P.ideal) :
    f * chartMonomial c d' - f' * chartMonomial c d ∈ P.ideal := by
  have hmul : den * (f * chartMonomial c d' - f' * chartMonomial c d) ∈ P.ideal := by
    have e : den * (f * chartMonomial c d' - f' * chartMonomial c d) =
        (den * f - num * chartMonomial c d) * chartMonomial c d' -
          (den * f' - num * chartMonomial c d') * chartMonomial c d := by ring
    rw [e]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ h) (P.ideal.mul_mem_right _ h')
  exact (P.isPrime.mem_or_mem hmul).resolve_left hden

theorem chartForm_mul_pow {P : ArithVariety n} {num₁ den₁ num₂ den₂ : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d₁ d₂ : ι → ℕ} {f₁ f₂ : MvPolynomial (Coord n) ℤ} (t : ℕ)
    (h₁ : den₁ * f₁ - num₁ * chartMonomial c d₁ ∈ P.ideal)
    (h₂ : den₂ * f₂ - num₂ * chartMonomial c d₂ ∈ P.ideal) :
    den₁ * den₂ ^ t * (f₁ * f₂ ^ t) - num₁ * num₂ ^ t * chartMonomial c (d₁ + t • d₂) ∈ P.ideal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h₁ h₂ ⊢
  rw [chartMonomial_add, chartMonomial_nsmul]
  simp only [map_mul, map_pow] at h₁ h₂ ⊢
  calc _ = (Ideal.Quotient.mk P.ideal den₁ * Ideal.Quotient.mk P.ideal f₁) *
        (Ideal.Quotient.mk P.ideal den₂ * Ideal.Quotient.mk P.ideal f₂) ^ t := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem deg_eq (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) :
    (((M.pow (q - k)).mul (HermLine.standard n)).pow t).deg +
        t • ((M.pow k).mul (HermLine.standard n).inv).deg = (M.pow (q * t)).deg := by
  ext i
  change (t • ((q - k) • M.deg + fun _ ↦ (1 : ℤ)) : ι → ℤ) i +
      (t • (k • M.deg + -fun _ ↦ (1 : ℤ)) : ι → ℤ) i = ((q * t) • M.deg : ι → ℤ) i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul, Nat.cast_sub hkq.le, Nat.cast_mul,
    Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply]
  ring

theorem metric_eq (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    (M.pow (q * t)).metric z = (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z *
        ((M.pow k).mul (HermLine.standard n).inv).metric z ^ t := by
  have hH := ((HermLine.standard n).metric_pos z hz).ne'
  simp only [HermLine.pow, HermLine.mul, HermLine.inv]
  rw [← mul_pow, pow_mul]
  congr 1
  have hq : M.metric z ^ q = M.metric z ^ (q - k) * M.metric z ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkq.le]
  rw [hq]
  field_simp

end SectionInjectivity

open SectionInjectivity in

theorem SectionInjectivity.proof : SectionInjectivity.Statement := by
  intro ι _ _ n P M k q hkq e C he0 heC t
  refine ⟨fun s hs ↦ ?_, fun s₁ s₂ h ↦ mul_right_cancel₀ (pow_ne_zero t he0) h⟩
  refine ⟨IntegralSection.cast (deg_eq M hkq t) (s.mul (e.pow t)), ?_, ?_⟩
  · simp only [IntegralSection.toFun, IntegralSection.cast, IntegralSection.mul, IntegralSection.pow,
      map_mul, map_pow]
    rw [div_pow, mul_div_mul_comm]
  · intro z hz c d f hcf hzc
    have hlive := isLive_of_mem_points hz hzc
    obtain ⟨d₁, f₁, hcf₁⟩ := s.regular c hlive
    obtain ⟨d₂, f₂, hcf₂⟩ := e.regular c hlive
    have hs₁ := hs z hz c d₁ f₁ hcf₁ hzc
    have he₂ := heC z hz c d₂ f₂ hcf₂ hzc
    have hf : s.den * e.den ^ t * f - s.num * e.num ^ t * chartMonomial c d ∈ P.ideal := hcf.2
    have hprod := chartForm_mul_pow t hcf₁.2 hcf₂.2
    have hden : s.den * e.den ^ t ∉ P.ideal :=
      (IntegralSection.cast (deg_eq M hkq t) (s.mul (e.pow t))).den_not_mem
    have hev := hz.2 _ (chartForm_cross hden hf hprod)
    have hμ := evalCone_chartMonomial_ne_zero hzc d
    have hμ₁ := evalCone_chartMonomial_ne_zero hzc d₁
    have hμ₂ := evalCone_chartMonomial_ne_zero hzc d₂
    rw [chartMonomial_add, chartMonomial_nsmul] at hev
    simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow] at hev hμ hμ₁ hμ₂ hs₁ he₂ ⊢
    rw [metric_eq M hkq t hz.1, Real.exp_zero]
    have hN := ((((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric_pos z hz.1)
    have hE := (((M.pow k).mul (HermLine.standard n).inv).metric_pos z hz.1)
    set x := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f
    set x₁ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f₁
    set x₂ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f₂
    set μ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d)
    set μ₁ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d₁)
    set μ₂ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d₂)
    set hNz := (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z
    set hEz := ((M.pow k).mul (HermLine.standard n).inv).metric z
    have hnorm : ‖x‖ * (‖μ₁‖ * ‖μ₂‖ ^ t) = ‖x₁‖ * ‖x₂‖ ^ t * ‖μ‖ := by
      have h := congrArg norm (sub_eq_zero.mp hev)
      simpa only [norm_mul, norm_pow] using h
    have hμ' := norm_pos_iff.mpr hμ
    have hμ₁' := norm_pos_iff.mpr hμ₁
    have hμ₂' := norm_pos_iff.mpr hμ₂
    have key : ‖x‖ / (‖μ‖ * (hNz * hEz ^ t)) = ‖x₁‖ / (‖μ₁‖ * hNz) * (‖x₂‖ / (‖μ₂‖ * hEz)) ^ t := by
      rw [div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (hNz * hEz ^ t) * hnorm
    rw [key]
    calc ‖x₁‖ / (‖μ₁‖ * hNz) * (‖x₂‖ / (‖μ₂‖ * hEz)) ^ t
        ≤ Real.exp (-(t * C)) * Real.exp C ^ t :=
          mul_le_mul hs₁ (pow_le_pow_left₀ (by positivity) he₂ t) (by positivity) (by positivity)
      _ = 1 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; simp

end

end GroundTheory.Heights₂.Heights
