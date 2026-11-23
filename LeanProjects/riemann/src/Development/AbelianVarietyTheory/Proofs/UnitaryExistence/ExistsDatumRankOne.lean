import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairing

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.RankOneDatum

theorem selfDual_of_perfect {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Submodule (𝓞 E) E) (ξ : E)
    (hfg : A.FG) (hne : A ≠ ⊥)
    (h : ∀ x : E, (∀ a ∈ A, ∀ b ∈ A, ∃ z : ℤ,
      Algebra.trace ℚ E (ξ * x * a * IsCMField.complexConj E b) = z) ↔ IsIntegral ℤ x) (x : E) :
    (∀ y ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ A := by
  constructor
  · intro hx
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨A, FractionalIdeal.isFractional_of_fg hfg⟩
    have hI : I ≠ 0 := fun h0 => hne (FractionalIdeal.coeToSubmodule_eq_bot.2 h0)
    have hc : ∀ c ∈ I⁻¹, IsIntegral ℤ (x * c) := fun c hc => (h _).1 fun a ha b hb => by
      have h1 : c * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hc ha
      rw [inv_mul_cancel₀ hI, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨u, hu⟩ := h1
      obtain ⟨n, hn⟩ := hx _ (A.smul_mem (IsCMField.ringOfIntegersComplexConj E u) hb)
      refine ⟨n, ?_⟩
      rw [← hn, Algebra.smul_def]
      congr 1
      have e : algebraMap (𝓞 E) E (IsCMField.ringOfIntegersComplexConj E u) = IsCMField.complexConj E (c * a) := by
        rw [← hu]; rfl
      rw [e, map_mul (IsCMField.complexConj E) _ b, IsCMField.complexConj_apply_apply]
      ring
    have h1 : (1 : E) ∈ I⁻¹ * I := by
      rw [inv_mul_cancel₀ hI]
      exact FractionalIdeal.one_mem_one _
    have h2 : x * 1 ∈ A := by
      refine FractionalIdeal.mul_induction_on (C := fun w => x * w ∈ A) h1 (fun c hc' a ha => ?_)
        (fun u v hu hv => ?_)
      · rw [← mul_assoc]
        exact A.smul_mem (⟨x * c, hc c hc'⟩ : 𝓞 E) ha
      · rw [mul_add]
        exact A.add_mem hu hv
    rwa [mul_one] at h2
  · intro hx y hy
    simpa using (h 1).2 isIntegral_one x hx y hy

set_option maxHeartbeats 1000000 in

theorem exists_datum_of_rt (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD) :
    ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 := by
  obtain ⟨A, hfg, hne, h⟩ := GlobalTheory.principalDatum_trace_perfect D
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hc : IsCMField.complexConj D.host.E D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hφ]
    simp
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
  have hd : (0 : ℝ) < Real.sqrt D.host.d := by
    rw [Real.sqrt_pos, Nat.cast_pos, Nat.pos_iff_ne_zero]
    intro h0
    have h1 := H.sqrt_neg_disc_sq
    rw [hrt0, hφ, h0] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨D₁, -, hp, hq, -⟩ := GlobalTheory.CM.SelfDualDatum.exists_datum D.host.E H A (-D.host.xi0) hfg hne
    (by
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hc, map_neg, map_one, map_natCast, mul_neg, div_neg])
    (fun τ hτ => by
      rw [hrt, hrt0, hφ] at hτ
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hτ, map_neg, map_one, map_natCast]
      generalize Ideal.absNorm D.host.ccK = N at hN ⊢
      generalize Real.sqrt D.host.d = s at hd ⊢
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have e : -(-1 / ((N : ℂ) * (Complex.I * (s : ℂ)))) = ((-(1 / (N * s)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        field_simp
        simp
      rw [e, Complex.mul_I_im, Complex.ofReal_re, neg_lt_zero]
      positivity)
    (fun x => by
      rw [← selfDual_of_perfect A D.host.xi0 hfg hne h x]
      refine forall₂_congr fun y _ => ?_
      rw [neg_mul, neg_mul, map_neg]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, hn]⟩)
  exact ⟨D₁, hp, hq⟩

theorem exists_datum_rank_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 :=
  fun D H _ _ _ h _ => exists_datum_of_rt D H h.rt h.rt0

end GlobalTheory.RankOneDatum
