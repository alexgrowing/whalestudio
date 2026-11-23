import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.IntCastMemRegMaxAt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalize.exists_prime_over {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hW : IsClosedPt W) :
    ∃ p : ℤ, Prime p ∧ ∀ k : ℤ, C k ∈ W ↔ p ∣ k := by
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  have : W.IsPrime := hW.1.1
  have : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.IsPrime.comap _
  refine ⟨_, Submodule.IsPrincipal.prime_generator_of_isPrime _ hvert, fun k => ?_⟩
  rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap]

theorem RegularityLocalize.proof (h₁ : RegularityLocalPrime.Statement) : RegularityLocalize.Statement := by
  classical
  intro K _ ι _ P W y hP hW hPW hy
  have hPp : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1
  have hφ : ∀ f : MRing ι, f ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0 :=
    fun f hf => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hf
  obtain ⟨p, hp, hpW⟩ := RegularityLocalize.exists_prime_over hP hW
  have hCpP : (C p : MRing ι) ∉ P := fun h => hp.ne_zero (by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rwa [hP.2.2.1, Ideal.mem_bot] at h')

  set S : Set (Ideal (MRing ι)) := {W' | IsClosedPt W' ∧ P ≤ W' ∧ C p ∈ W'} with hS
  have hSfin : S.Finite := (divSupp_finite P (C p)).subset fun W' hW' =>
    (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W' hP (RegularityDenominator.isMultiHomog_C p) hCpP).2 hW'
  have hWS : W ∈ S := ⟨hW, hPW, (hpW p).2 dvd_rfl⟩
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSfin fun W' hW' => hW'.1.1

  obtain ⟨u₀, v₀, a, hu₀, hv₀, hv₀W, hyv₀⟩ := LocRingFrac.proof K ι P W hPp hWp hPW y hy
  choose c hc using hW.1.2.2
  obtain ⟨t, ht, htW⟩ : ∃ t : MRing ι, IsMultiHomog t 1 ∧ t ∉ W :=
    ⟨_, AvoidRing.isMultiHomog_coordProd c 1, AvoidRing.coordProd_not_mem hWp c hc 1⟩
  obtain ⟨u, v, hu, hv, hvW, hyv⟩ : ∃ u v : MRing ι, IsMultiHomog u (a + 1) ∧ IsMultiHomog v (a + 1) ∧ v ∉ W ∧
      y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) :=
    ⟨u₀ * t, v₀ * t, AvoidRing.isMultiHomog_mul hu₀ ht, AvoidRing.isMultiHomog_mul hv₀ ht,
      fun h => (hWp.mem_or_mem h).elim hv₀W htW, by simp only [map_mul, ← mul_assoc, hyv₀]⟩

  set m := ∑ k, d₀ k
  obtain ⟨h, hh, hhS⟩ := hd₀ ((m + 1) • (a + 1)) fun k => by
    have h1 : d₀ k ≤ m := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    nlinarith
  have hhW : h ∉ W := hhS W hWS
  have hhP : h ∉ P := fun e => hhW (hPW e)
  have hvm : IsMultiHomog (v ^ (m + 1)) ((m + 1) • (a + 1)) := AvoidRing.isMultiHomog_pow hv _
  have hxm : IsMultiHomog (v ^ m * u) ((m + 1) • (a + 1)) := by
    rw [succ_nsmul]; exact AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_pow hv _) hu
  obtain ⟨s₀, hs₀⟩ := exists_funField_mul_eq hvm hh hhP
  obtain ⟨x₀, hx₀⟩ := exists_funField_mul_eq hxm hh hhP
  have hys : y * (s₀ : FractionRing (MRing ι ⧸ P)) = x₀ := by
    refine mul_right_cancel₀ (hφ h hhP) ?_
    rw [mul_assoc, hs₀, hx₀]
    simp only [map_pow, map_mul]
    rw [pow_succ, ← hyv]
    ring

  have hover : ∀ z : funField P, (∃ g : MRing ι, IsMultiHomog g ((m + 1) • (a + 1)) ∧
      (z : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P h) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
      ∀ W', IsClosedPt W' → P ≤ W' → C p ∈ W' → (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W' :=
    fun z ⟨g, hg, hz⟩ W' h1 h2 h3 => frac_mem_locRing h2 hg hh (hhS W' ⟨h1, h2, h3⟩) hz
  obtain ⟨n₁, hn₁, hs⟩ := h₁ K ι P p s₀ hP hp (hover s₀ ⟨_, hvm, hs₀⟩)
  obtain ⟨n₂, hn₂, hx⟩ := h₁ K ι P p x₀ hP hp (hover x₀ ⟨_, hxm, hx₀⟩)
  have hsc : (((n₂ : regRing P) * ⟨_, hs⟩ : regRing P) : funField P) = (n₂ : funField P) * ((n₁ : funField P) * s₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  have hxc : (((n₁ : regRing P) * ⟨_, hx⟩ : regRing P) : funField P) = (n₁ : funField P) * ((n₂ : funField P) * x₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  refine ⟨(n₂ : regRing P) * ⟨_, hs⟩, (n₁ : regRing P) * ⟨_, hx⟩, ?_, ?_⟩
  ·
    have hnW : (C (n₁ * n₂) : MRing ι) ∉ W := fun e => by
      rcases hp.dvd_or_dvd ((hpW _).1 e) with h' | h'
      exacts [hn₁ h', hn₂ h']
    have hden : IsMultiHomog (C (n₁ * n₂) * v ^ (m + 1)) ((m + 1) • (a + 1)) := by
      simpa using AvoidRing.isMultiHomog_mul (RegularityDenominator.isMultiHomog_C (n₁ * n₂)) hvm
    have hdenW : C (n₁ * n₂) * v ^ (m + 1) ∉ W := fun e =>
      (hWp.mem_or_mem e).elim hnW fun e' => hvW (hWp.mem_of_pow_mem _ e')
    have hden0 := hφ _ fun e => hdenW (hPW e)
    refine ⟨_, frac_mem_locRing hPW hh hden hdenW (div_mul_cancel₀ _ hden0), ?_⟩
    rw [hsc, mul_div_assoc', div_eq_one_iff_eq hden0]
    simp only [map_mul, eq_intCast C, map_intCast, Int.cast_mul, Subring.coe_mul, Subring.coe_intCast, ← hs₀]
    ring
  · rw [hsc, hxc]
    simp only [Subring.coe_mul, Subring.coe_intCast, ← hys]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
