import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.WhittakerHecke.SatakeParamMulEqCentralCharPowInertiaDeg
import Development.AutomorphicArithmetic.WhittakerHecke.GoodPrimeSplitOrInertOfQuadratic
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatHeightOneSpectrumNormVEqPrimeBadIffDvd
import Development.AutomorphicArithmetic.WhittakerHecke.FalseOfLandauNonnegEulerFactorsEntire

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.A.LanSer

open PowerSeries

private noncomputable def hh (τ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => τ
  | n + 2 => τ * hh τ (n + 1) - hh τ n

private noncomputable def gg (τ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => τ ^ 2
  | n + 2 => gg τ n + hh τ (n + 2) ^ 2

private theorem gg_nonneg (τ : ℝ) : ∀ n, 0 ≤ gg τ n
  | 0 => by simp [gg]
  | 1 => by simp only [gg]; positivity
  | n + 2 => by
    have := gg_nonneg τ n
    simp only [gg]
    positivity

private theorem one_le_gg (τ : ℝ) : 1 ≤ gg τ 2 := by
  simp only [gg]
  nlinarith [sq_nonneg (hh τ 2)]

private theorem hh_rec (τ : ℝ) (n : ℕ) :
    hh τ (n + 3) ^ 2 - (τ ^ 2 - 1) * hh τ (n + 2) ^ 2 + (τ ^ 2 - 1) * hh τ (n + 1) ^ 2 - hh τ n ^ 2 = 0 := by
  have h2 : hh τ (n + 2) = τ * hh τ (n + 1) - hh τ n := rfl
  have h3 : hh τ (n + 3) = τ * hh τ (n + 2) - hh τ (n + 1) := rfl
  rw [h3, h2]
  ring

private noncomputable def Gs (τ : ℝ) : PowerSeries ℂ := mk fun k => (gg τ k : ℂ)
private noncomputable def Qs (τ : ℝ) : PowerSeries ℂ := mk fun k => ((hh τ k ^ 2 : ℝ) : ℂ)

private theorem Gs_mul (τ : ℝ) : Gs τ * (1 - X ^ 2) = Qs τ := by
  have e : Gs τ * (1 - X ^ 2) = Gs τ - Gs τ * X ^ 2 := by ring
  rw [e]
  ext n
  rcases n with _ | _ | n
  · simp [Gs, Qs, coeff_mul_X_pow', gg, hh]
  · simp [Gs, Qs, coeff_mul_X_pow', gg, hh]
  · have : gg τ (n + 2) = gg τ n + hh τ (n + 2) ^ 2 := rfl
    simp [Gs, Qs, coeff_mul_X_pow', this]

private theorem Qs_mul (τ : ℝ) (a : ℂ) (ha : a = (τ : ℂ) ^ 2 - 1) :
    Qs τ * (1 - C a * X + C a * X ^ 2 - X ^ 3) = 1 + X := by
  have e : Qs τ * (1 - C a * X + C a * X ^ 2 - X ^ 3) =
      Qs τ - C a * (Qs τ * X ^ 1) + C a * (Qs τ * X ^ 2) - Qs τ * X ^ 3 := by ring
  rw [e]
  ext n
  rcases n with _ | _ | _ | n
  · simp [Qs, coeff_mul_X_pow', hh, coeff_X, coeff_one]
  · simp [Qs, coeff_mul_X_pow', hh, coeff_X, coeff_one]
    subst ha
    ring
  · simp [Qs, coeff_mul_X_pow', hh, coeff_X, coeff_one]
    subst ha
    ring
  · have := congrArg (fun x : ℝ => (x : ℂ)) (hh_rec τ n)
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_zero] at this
    simp [Qs, coeff_mul_X_pow', coeff_X, coeff_one]
    subst ha
    linear_combination this

private noncomputable def Dp (τ : ℝ) : PowerSeries ℂ := (1 - X) ^ 2 * (1 - C ((τ : ℂ) ^ 2 - 2) * X + X ^ 2)

private theorem one_add_X_ne : (1 + X : PowerSeries ℂ) ≠ 0 := fun h => by
  have := congrArg (coeff 0) h
  simp at this

private theorem Gs_Dp (τ : ℝ) : Gs τ * Dp τ = 1 := by
  refine mul_right_cancel₀ one_add_X_ne ?_
  have hC : C ((τ : ℂ) ^ 2 - 1) = C ((τ : ℂ) ^ 2 - 2) + (1 : PowerSeries ℂ) := by
    rw [← map_one (C (R := ℂ)), ← map_add]
    congr 1
    ring
  calc Gs τ * Dp τ * (1 + X) = (Gs τ * (1 - X ^ 2)) * (1 - C ((τ : ℂ) ^ 2 - 1) * X + C ((τ : ℂ) ^ 2 - 1) * X ^ 2 - X ^ 3) := by
        rw [Dp, hC]
        ring
    _ = 1 * (1 + X) := by rw [Gs_mul, Qs_mul τ _ rfl, one_mul]

private theorem eq_Gs {τ : ℝ} {S : PowerSeries ℂ} (h : S * Dp τ = 1) : S = Gs τ := by
  calc S = S * (Gs τ * Dp τ) := by rw [Gs_Dp, mul_one]
    _ = (S * Dp τ) * Gs τ := by ring
    _ = Gs τ := by rw [h, one_mul]

private theorem lin_mul (p q : ℂ) (Y : PowerSeries ℂ) :
    (1 - C p * Y) * (1 - C q * Y) = (1 - C (p + q) * Y + C (p * q) * Y ^ 2 : PowerSeries ℂ) := by
  rw [map_add, map_mul]
  ring

private theorem tau_sq {α β c : ℂ} (h1 : starRingEnd ℂ (α + β) * (α * β) = α + β) (hc : c * (α * β) = 1) :
    c * (α + β) ^ 2 = (‖α + β‖ : ℂ) ^ 2 := by
  rw [← Complex.mul_conj']
  calc c * (α + β) ^ 2 = (α + β) * (c * (starRingEnd ℂ (α + β) * (α * β)) * 1) * 1 + 0 := by
        rw [h1]; ring
    _ = (α + β) * starRingEnd ℂ (α + β) := by
        linear_combination ((α + β) * starRingEnd ℂ (α + β)) * hc

private theorem Gs_sq (τ : ℝ) : (∀ k, 0 ≤ coeff k (Gs τ * Gs τ)) ∧ 1 ≤ coeff 4 (Gs τ * Gs τ) := by
  have e : ∀ k, coeff k (Gs τ * Gs τ) = ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, gg τ p.1 * gg τ p.2 : ℝ) : ℂ) := fun k => by
    simp [Gs, coeff_mul]
  have hp : ∀ p : ℕ × ℕ, 0 ≤ gg τ p.1 * gg τ p.2 := fun p => mul_nonneg (gg_nonneg τ _) (gg_nonneg τ _)
  refine ⟨fun k => ?_, ?_⟩
  · rw [e]
    exact Complex.zero_le_real.2 (Finset.sum_nonneg fun p _ => hp p)
  · rw [e, ← Complex.ofReal_one, Complex.real_le_real]
    have h1 : gg τ 2 * gg τ 2 ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 4, gg τ p.1 * gg τ p.2 :=
      Finset.single_le_sum (f := fun p : ℕ × ℕ => gg τ p.1 * gg τ p.2) (fun p _ => hp p)
        (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl : ((2, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal 4)
    nlinarith [one_le_gg τ]

private theorem serSplit {α β c : ℂ} {S S' : PowerSeries ℂ} (h1 : starRingEnd ℂ (α + β) * (α * β) = α + β) (hc : c * (α * β) = 1)
    (hS : S * ((1 - C (α * α * c) * X) * (1 - C (α * β * c) * X) * (1 - C (β * α * c) * X) * (1 - C (β * β * c) * X)) = 1)
    (hS' : S' * ((1 - C (α * α * c) * X) * (1 - C (α * β * c) * X) * (1 - C (β * α * c) * X) * (1 - C (β * β * c) * X)) = 1) :
    (∀ k, 0 ≤ coeff k (S * S')) ∧ 1 ≤ coeff 4 (S * S') := by
  have e : ((1 - C (α * α * c) * X) * (1 - C (α * β * c) * X) * (1 - C (β * α * c) * X) * (1 - C (β * β * c) * X) : PowerSeries ℂ) =
      Dp ‖α + β‖ := by
    have hs : α * α * c + β * β * c = ((‖α + β‖ : ℝ) : ℂ) ^ 2 - 2 := by
      rw [← tau_sq h1 hc]
      linear_combination (-2 : ℂ) * hc
    have hq : α * α * c * (β * β * c) = 1 := by
      linear_combination (c * (α * β) + 1) * hc
    have h2 : α * β * c = 1 := by rw [← hc]; ring
    have h3 : β * α * c = 1 := by rw [← hc]; ring
    rw [h2, h3, Dp, ← hs, map_one]
    have := lin_mul (α * α * c) (β * β * c) X
    rw [hq, map_one] at this
    linear_combination ((1 - X) ^ 2 : PowerSeries ℂ) * this
  rw [e] at hS hS'
  rw [eq_Gs hS, eq_Gs hS']
  exact Gs_sq _

private theorem serInert {α β c : ℂ} {S S' : PowerSeries ℂ} (h1 : starRingEnd ℂ (α + β) * (α * β) = α + β) (hc : c * c * (α * β) = 1)
    (hS : S * ((1 - C (α * c) * X) * (1 - C (β * c) * X) * (1 - X ^ 2)) = 1)
    (hS' : S' * ((1 - C (α * -c) * X) * (1 - C (β * -c) * X) * (1 - X ^ 2)) = 1) :
    (∀ k, 0 ≤ coeff k (S * S')) ∧ 1 ≤ coeff 4 (S * S') := by
  set τ := ‖α + β‖ with hτ
  have hs : α * α * (c * c) + β * β * (c * c) = (τ : ℂ) ^ 2 - 2 := by
    rw [hτ, ← tau_sq h1 hc]
    linear_combination (-2 : ℂ) * hc
  have hq : α * α * (c * c) * (β * β * (c * c)) = 1 := by
    linear_combination (c * c * (α * β) + 1) * hc
  have hD : (S * S') * expand 2 two_ne_zero (Dp τ) = 1 := by
    have e1 : expand 2 two_ne_zero (Dp τ) = (1 - X ^ 2) ^ 2 * (1 - C ((τ : ℂ) ^ 2 - 2) * X ^ 2 + (X ^ 2) ^ 2) := by
      rw [Dp]
      generalize (τ : ℂ) ^ 2 - 2 = b
      simp only [map_mul, map_sub, map_add, map_pow, map_one, expand_C, expand_X]
    have L := lin_mul (α * α * (c * c)) (β * β * (c * c)) (X ^ 2)
    rw [hs, hq, map_one] at L
    have hp : C (α * α * (c * c)) = C (α * c) * C (α * c) := by
      rw [← map_mul]
      congr 1
      ring
    have hp' : C (β * β * (c * c)) = C (β * c) * C (β * c) := by
      rw [← map_mul]
      congr 1
      ring
    have hn : C (α * -c) = -C (α * c) := by rw [mul_neg, map_neg]
    have hn' : C (β * -c) = -C (β * c) := by rw [mul_neg, map_neg]
    rw [hp, hp'] at L
    rw [hn, hn'] at hS'
    calc (S * S') * expand 2 two_ne_zero (Dp τ) =
        (S * ((1 - C (α * c) * X) * (1 - C (β * c) * X) * (1 - X ^ 2))) *
          (S' * ((1 - -C (α * c) * X) * (1 - -C (β * c) * X) * (1 - X ^ 2))) := by
          rw [e1]
          linear_combination (-(S * S') * (1 - X ^ 2) ^ 2) * L
      _ = 1 := by rw [hS, hS', one_mul]
  have hG : S * S' = expand 2 two_ne_zero (Gs τ) := by
    calc S * S' = (S * S') * expand 2 two_ne_zero (Gs τ * Dp τ) := by rw [Gs_Dp, map_one, mul_one]
      _ = ((S * S') * expand 2 two_ne_zero (Dp τ)) * expand 2 two_ne_zero (Gs τ) := by rw [map_mul]; ring
      _ = expand 2 two_ne_zero (Gs τ) := by rw [hD, one_mul]
  rw [hG]
  refine ⟨fun k => ?_, ?_⟩
  · rw [coeff_expand]
    split_ifs
    · simpa [Gs] using Complex.zero_le_real.2 (gg_nonneg τ (k / 2))
    · exact le_rfl
  · rw [coeff_expand, if_pos (by norm_num)]
    have := one_le_gg τ
    simp only [Gs, coeff_mk, show 4 / 2 = 2 from rfl]
    rw [← Complex.ofReal_one, Complex.real_le_real]
    exact this

end UpperTheory.ConvolutionTheory.RankTwoDescent.A.LanSer

open UpperTheory.ConvolutionTheory.RankTwoDescent.A.LanSer in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.lan_of :
    SatU → Landau → Lan := by
  intro hS hL E _ _ _ D P ω χ hC hU hχ η hχe Lv N φ hG hη hB hc hc' a a' ha ha' hs hs' he he'
  subst hχe
  refine UpperTheory.false_of_landau_nonneg_euler_factors_entire a a' N hG.pos ha.one ha'.one ha.mul ha'.mul ha.bad ha'.bad ?_ hs hs' he he' hL
  intro p hp hpN
  obtain ⟨v, hv, hbad⟩ := UpperTheory.exists_rat_heightOneSpectrum_normV_eq_prime_bad_iff_dvd p N hp
  have hnb : ¬ Bad N v := fun h => hpN (hbad.1 h)
  have hnL : ¬ Bad Lv v := fun h => hnb (by
    obtain ⟨m, hm⟩ := hG.dvd
    unfold Bad at h ⊢
    rw [hm]; push_cast; exact Ideal.mul_mem_right _ _ h)
  obtain ⟨⟨w, hw⟩, hall⟩ := UpperTheory.good_prime_split_or_inert_of_quadratic E D v (hG.pl v hnb)
  have hnw : ¬ Bad N (w.under (𝓞 ℚ)) := by rw [hw]; exact hnb
  have hnw' : ¬ Bad Lv (w.under (𝓞 ℚ)) := by rw [hw]; exact hnL
  have hvp : ∀ k, normV v ^ k = p ^ k := fun k => by rw [hv]
  have hcard : ∀ w₁ : H.P E, ∀ B, (CG.mk P).HasSat w₁ B → ∃ α β : ℂˣ, B = {α, β} := fun w₁ B h =>
    Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w₁ B).1 h))
  have hval : (ω⁻¹).val v = (ω.val v)⁻¹ := HChar.val_inv ω v
  rcases hall w hw with ⟨hn, w', hne, hw'⟩ | hn
  · obtain ⟨B, h1, h2⟩ := hB w w' hnw (hw'.trans hw.symm)
    obtain ⟨α, β, rfl⟩ := hcard w B h1
    obtain ⟨-, hcj, -⟩ := hS E D P ω ω⁻¹ hC hU hχ w α β h1
    have hab := UpperTheory.satake_param_mul_eq_central_char_pow_inertiaDeg E P ω Lv hC hc w α β 1 hnw' (by rw [hw, pow_one]; exact hn) h1
    rw [hw, pow_one] at hab
    have hetav : η.val v = 1 := by
      have := hη w hnw
      rw [hw, if_pos hn] at this
      exact this
    have hval' : ((ω * η)⁻¹).val v = (ω.val v)⁻¹ := by
      rw [HChar.val_inv, HChar.val_mul, hetav, mul_one]
    have e1 := ha.split v hnb w w' hne.symm hw hw' α β α β h1 h2
    have e2 := ha'.split v hnb w w' hne.symm hw hw' α β α β h1 h2
    rw [hval] at e1
    rw [hval'] at e2
    simp only [hvp, Units.val_mul] at e1 e2
    refine serSplit (α := α) (β := β) (c := ((ω.val v)⁻¹ : ℂˣ)) hcj ?_ e1 e2
    rw [← Units.val_mul, ← Units.val_mul, hab]; simp
  · obtain ⟨B, h1, -⟩ := hB w w hnw rfl
    obtain ⟨α, β, rfl⟩ := hcard w B h1
    obtain ⟨-, hcj, -⟩ := hS E D P ω ω⁻¹ hC hU hχ w α β h1
    have hab := UpperTheory.satake_param_mul_eq_central_char_pow_inertiaDeg E P ω Lv hC hc w α β 2 hnw' (by rw [hw]; exact hn) h1
    rw [hw] at hab
    have hne1 : normV w ≠ normV v := by
      rw [hn, hv]
      have := hp.two_le
      nlinarith
    have hetav : η.val v = -1 := by
      have := hη w hnw
      rw [hw, if_neg hne1] at this
      exact this
    have hval' : ((ω * η)⁻¹).val v = -(ω.val v)⁻¹ := by
      rw [HChar.val_inv, HChar.val_mul, hetav]; simp
    have e1 := ha.inert v hnb w hw hn α β h1
    have e2 := ha'.inert v hnb w hw hn α β h1
    rw [hval] at e1
    rw [hval'] at e2
    simp only [hvp, Units.val_mul, Units.val_neg] at e1 e2
    refine serInert (α := α) (β := β) (c := ((ω.val v)⁻¹ : ℂˣ)) hcj ?_ e1 e2
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hab]; simp [pow_two]
