import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem subring_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R₁ R₂ : Subring F}
    (h₁ : B ≤ R₁) (h₂ : B ≤ R₂) (𝔭 : Ideal B) [𝔭.IsPrime]
    (hl₁ : letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭)
    (hl₂ : letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) : R₁ = R₂ := by
  have key : ∀ (R₁ R₂ : Subring F) (h₁ : B ≤ R₁) (h₂ : B ≤ R₂),
      (letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭) →
      (letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) → R₁ ≤ R₂ := by
    intro R₁ R₂ h₁ h₂ hl₁ hl₂ z hz
    let _ := (Subring.inclusion h₁).toAlgebra
    let _ := (Subring.inclusion h₂).toAlgebra
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔭.primeCompl (⟨z, hz⟩ : R₁)
    obtain ⟨t, ht⟩ := (IsLocalization.map_units R₂ s).exists_right_inv
    have e₁ : z * ((s : B) : F) = ((b : B) : F) := congrArg Subtype.val hbs
    have e₂ : ((s : B) : F) * (t : F) = 1 := congrArg Subtype.val ht
    have hzt : z = (b : F) * t := by
      calc z = z * (((s : B) : F) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : B) : F)) * t := by ring
        _ = (b : F) * t := by rw [e₁]
    rw [hzt]
    exact R₂.mul_mem (h₂ b.2) t.2
  exact le_antisymm (key R₁ R₂ h₁ h₂ hl₁ hl₂) (key R₂ R₁ h₂ h₁ hl₂ hl₁)

theorem prime_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMax.proof (h₁ : BlowUpOverLocMaxPoint.Statement.{u})
    (h₂ : BlowUpOverLocPointMax.Statement.{u}) (h₃ : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  have hpt := h₁ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hmx := h₂ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  choose f hfT hfloc hfdeg using
    fun 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} => hpt 𝔫.1 𝔫.2

  have hmh : ∀ W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes, IsMultiHomogIdeal W' :=
    fun W' hW' => MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  refine ⟨Equiv.ofBijective (fun 𝔫 => ⟨f 𝔫, hfT 𝔫⟩) ⟨?_, ?_⟩, fun 𝔫 => ⟨hfloc 𝔫, hfdeg 𝔫⟩⟩
  ·
    intro 𝔫₁ 𝔫₂ h12
    have hf : f 𝔫₁ = f 𝔫₂ := congrArg Subtype.val h12
    have hl₁ := hfloc 𝔫₁
    rw [hf] at hl₁
    obtain ⟨k₁, l₁⟩ := hl₁
    obtain ⟨k₂, l₂⟩ := hfloc 𝔫₂
    have := 𝔫₁.2.isPrime
    have := 𝔫₂.2.isPrime
    exact Subtype.ext (prime_eq_of_isLocalization_atPrime k₂ 𝔫₁.1 𝔫₂.1 l₁ l₂)
  ·
    rintro ⟨W', hW'⟩
    obtain ⟨k, 𝔫, h𝔫, hl⟩ := hmx W' hW'.1 hW'.2.1 hW'.2.2
    refine ⟨⟨𝔫, h𝔫⟩, Subtype.ext ?_⟩
    obtain ⟨k', hl'⟩ := hfloc ⟨𝔫, h𝔫⟩
    have := h𝔫.isPrime
    have hring : blowUpLocRing P u (f ⟨𝔫, h𝔫⟩) = blowUpLocRing P u W' :=
      subring_eq_of_isLocalization_atPrime k' k 𝔫 hl' hl
    have hT := hfT ⟨𝔫, h𝔫⟩
    exact h₃ O K ι J P u _ _ hT.1.1.1 (hmh _ hT.1) hT.2.1 (le_trans le_sup_left hT.1.1.2)
      hW'.1.1.1 (hmh _ hW'.1) hW'.2.1 (le_trans le_sup_left hW'.1.1.2) hring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
