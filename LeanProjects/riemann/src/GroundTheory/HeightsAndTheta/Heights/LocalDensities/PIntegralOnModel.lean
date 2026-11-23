import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

theorem exists_prime_mul_eq_of_not_dvd {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hab : ¬ b ∣ a) :
    ∃ P : Ideal A, P.IsPrime ∧ ∃ w ∉ P, ∃ c ∈ P, w * b = c * a := by
  classical
  by_cases hb : b = 0
  · refine ⟨⊥, Ideal.isPrime_bot, 1, ?_, 0, (⊥ : Ideal A).zero_mem, by simp [hb]⟩
    rw [Submodule.mem_bot]
    exact one_ne_zero
  let N : Submodule A (A ⧸ Ideal.span {b}) := Submodule.span A {Ideal.Quotient.mk _ a}
  let n₀ : N := ⟨Ideal.Quotient.mk _ a, Submodule.subset_span rfl⟩
  have hn₀ : n₀ ≠ 0 := by
    intro h
    apply hab
    have : Ideal.Quotient.mk (Ideal.span {b}) a = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A n₀ hn₀
  obtain ⟨hPp, ⟨m, hm⟩, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hm
  obtain ⟨y, hy⟩ : ∃ y, y = x * a := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.coe_inj]
    show r • (x • Ideal.Quotient.mk (Ideal.span {b}) a) = 0 ↔ b ∣ r * y
    rw [smul_smul, GroundTheory.Arith.Toric.smul_mk_eq_zero_iff, hy, mul_assoc]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let M : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hMfg : M.FG := (IsNoetherian.noetherian P).map _
    have hM0 : M ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ M := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule M hM0 hMfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    refine ⟨P, hPp, s₀, hs₀, r₀ * x, P.mul_mem_right x hr₀, ?_⟩
    rw [mul_assoc, ← hy, hrs, mul_comm]

theorem IntegralOnModel.proof (hpt : IntegralPointThroughPrime.Statement) :
    IntegralOnModel.Statement := by
  intro F _ _ R _ _ _ _ _ _ r g s ⟨hs, hg, hpts⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  by_contra hndvd
  have hnd : ¬ algebraMap (𝓞 F) R s ∣ r := fun ⟨r', h⟩ => hndvd ⟨r', h⟩
  obtain ⟨P, hP, w, hw, c, hc, hwc⟩ := exists_prime_mul_eq_of_not_dvd hnd
  have hsP : algebraMap (𝓞 F) R s ∈ P := by
    have : w * algebraMap (𝓞 F) R s ∈ P := hwc ▸ P.mul_mem_right r hc
    exact (hP.mem_or_mem this).resolve_left hw
  have hpP : (P.comap (algebraMap (𝓞 F) R)).IsPrime := Ideal.comap_isPrime _ P
  have hp0 : P.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
    intro h
    have : s ∈ P.comap (algebraMap (𝓞 F) R) := hsP
    rw [h, Submodule.mem_bot] at this
    exact hs this
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.comap (algebraMap (𝓞 F) R), hpP, hp0⟩
  obtain ⟨L, _, _, _, y, hcomp, hint, hyg, ⟨bw, hbw, hbwint⟩, hPnon⟩ :=
    hpt F R v P w g ⟨hP, rfl, hw, hg⟩
  have hys : y (algebraMap (𝓞 F) R s) ≠ 0 := by
    rw [← RingHom.comp_apply, hcomp]
    simp only [RingHom.comp_apply, ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hs
  have hyr := hpts v L y hcomp hint hyg
  apply hPnon c hc (y r / y (algebraMap (𝓞 F) R s) * bw) _ (RingHom.IsIntegralElem.mul _ hyr hbwint)
  have h1 : y w * y (algebraMap (𝓞 F) R s) = y c * y r := by rw [← map_mul, ← map_mul, hwc]
  calc y r / y (algebraMap (𝓞 F) R s) * bw * y c
      = bw * y w * ((y c * y r) / (y w * y (algebraMap (𝓞 F) R s))) := by
        have hyw : y w ≠ 0 := fun h0 => by simp [h0] at hbw
        field_simp
    _ = 1 := by rw [hbw, ← h1, div_self (mul_ne_zero (fun h0 => by simp [h0] at hbw) hys), one_mul]

end GroundTheory.Heights₂.Heights.FourB
