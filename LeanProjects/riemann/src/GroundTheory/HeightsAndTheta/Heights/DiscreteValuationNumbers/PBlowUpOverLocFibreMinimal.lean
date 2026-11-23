import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocPointLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocFibreMinimal.proof (h₁ : BlowUpOverLocPointLoc.Statement.{u})
    (h₂ : BlowUpLocRingInj.Statement.{u}) : BlowUpOverLocFibreMinimal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  have := hP.multiProj.isPrime
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hxW' : liftForm x ∈ W' := by
    rw [← Ideal.mem_comap, hW'c]
    exact hxW
  have hle : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ W' :=
    sup_le hW'le ((Ideal.span_singleton_le_iff_mem _).mpr hxW')
  refine ⟨⟨hW'p, hle⟩, fun Q hQ hQW' => ?_⟩
  have := hQ.1
  obtain ⟨Q₀, hQ₀min, hQ₀Q⟩ := Ideal.exists_minimalPrimes_le hQ.2
  have hQ₀W' : Q₀ ≤ W' := hQ₀Q.trans hQW'
  have hQ₀p : Q₀.IsPrime := hQ₀min.1.1
  have hQ₀h : IsMultiHomogIdeal Q₀ :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ Q₀
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hQ₀min
  have hQ₀r : IsRelevant Q₀ := fun k => by
    obtain ⟨i, hi⟩ := hW'r k
    exact ⟨i, fun h => hi (hQ₀W' h)⟩
  have hQ₀le : blowUpOf P u ≤ Q₀ := le_sup_left.trans hQ₀min.1.2
  have hQ₀c : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) = W := by
    obtain ⟨hcp, hPc, -, -⟩ := comap_liftForm_facts hQ₀p hQ₀le hQ₀r
    have hxc : x ∈ Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) :=
      hQ₀min.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hcW : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := hW'c ▸ Ideal.comap_mono hQ₀W'
    exact le_antisymm hcW (hWmin.2 ⟨hcp, sup_le hPc ((Ideal.span_singleton_le_iff_mem _).mpr hxc)⟩ hcW)
  obtain ⟨h, 𝔫, h𝔫, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h₀, 𝔮, h𝔮, hl₀⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel Q₀ hQ₀p hQ₀h hQ₀r hQ₀le hQ₀c
  have hsub : blowUpLocRing P u W' ≤ blowUpLocRing P u Q₀ := by
    refine Subring.closure_mono ?_
    rintro z ⟨b, F, G, hF, hG, hGW', hz⟩
    exact ⟨b, F, G, hF, hG, fun hGQ => hGW' (hQ₀W' hGQ), hz⟩
  let _ := (Subring.inclusion h).toAlgebra
  let _ := (Subring.inclusion h₀).toAlgebra
  have := h𝔫.isPrime
  have := h𝔮.isPrime
  have : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫 := hl
  have : IsLocalization.AtPrime (blowUpLocRing P u Q₀) 𝔮 := hl₀
  have : IsLocalRing (blowUpLocRing P u Q₀) := IsLocalization.AtPrime.isLocalRing _ 𝔮
  have hq : 𝔮 ≤ 𝔫 := by
    intro s hs
    by_contra hsn
    have hu1 : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') s) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ ⟨s, hsn⟩
    have hu2 : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u Q₀) s) :=
      hu1.map (Subring.inclusion hsub)
    have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (blowUpLocRing P u Q₀) 𝔮 s).mpr hs
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu2
  have hqn : 𝔮 = 𝔫 := h𝔮.eq_of_le h𝔫.ne_top hq
  have hsup : blowUpLocRing P u Q₀ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl
      (⟨z, hz⟩ : blowUpLocRing P u Q₀)
    replace hbs : IsLocalization.mk' (blowUpLocRing P u Q₀) b s = ⟨z, hz⟩ := hbs
    have hs : (s : blowUpOverLoc P W u) ∈ 𝔫.primeCompl := hqn ▸ s.2
    obtain ⟨v, hv⟩ : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') s) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ ⟨s, hs⟩
    have e1 : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) =
        ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) := by
      have := congrArg Subtype.val (IsLocalization.mk'_spec (blowUpLocRing P u Q₀) b s)
      rw [hbs] at this
      exact this
    have e2 : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) *
        (((v⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W') : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have e3 : z = ((algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') b *
        ((v⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W') : blowUpLocRing P u W') :
          FractionRing (MRing ι O ⧸ P)) := by
      rw [Subring.coe_mul, ← mul_one z, ← e2, ← mul_assoc, e1]
      rfl
    rw [e3]
    exact Subtype.property _
  have heq : Q₀ = W' :=
    h₂ O K ι J P u Q₀ W' hQ₀p hQ₀h hQ₀r hQ₀le hW'p hW'h hW'r hW'le (le_antisymm hsup hsub)
  rw [← heq]
  exact hQ₀Q

end

end GroundTheory.Heights₂.Heights.NumbersDVR
