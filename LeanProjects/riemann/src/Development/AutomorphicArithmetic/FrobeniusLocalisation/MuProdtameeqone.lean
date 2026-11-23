import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsRationalUnitaryDeterminantMap
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuSplitsCfacts
import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne

open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory

theorem UpperTheory.HF.Formalism.HC.HostAx.prod_tame_eq_one :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → SplitsC H.E p → ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal →
      ∀ (ω : (ZMod p)ˣ →* ℂˣ) (θ : ∀ w : HeightOneSpectrum (𝓞 H.E), (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ),
      (∀ w ∈ aboveF (L := H.E) H.K Q, ∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 H.E ⧸ w.asIdeal)ˣ),
        (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) → θ w b = ω (ZMod.unitOfCoprime a ha)) →
      ∀ ζ : (𝓞 H.E)ˣ, H.IsMu ((ζ : 𝓞 H.E) : H.E) →
        ∏ w ∈ aboveF (L := H.E) H.K Q, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
  intro φ H p hp hs Q hQ ω θ hθ ζ hζ
  have hG : IsGalois ℚ H.E := H.galois
  have hGK : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  have memS : ∀ w, w ∈ aboveF (L := H.E) H.K Q ↔ w.under (𝓞 H.K) = Q := fun w => by
    rw [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have overp : ∀ w ∈ aboveF (L := H.E) H.K Q, ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal := by
    intro w hw
    have h1 : ((p : ℕ) : 𝓞 H.K) ∈ (w.under (𝓞 H.K)).asIdeal := by rw [(memS w).1 hw]; exact hQ
    have h2 : ((p : ℕ) : 𝓞 H.K) ∈ Ideal.under (𝓞 H.K) w.asIdeal := h1
    rw [Ideal.mem_under, map_natCast] at h2
    exact h2
  refine UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E p hp Q _ memS (fun w hw => ?_) ω θ (fun w hw a ha => ?_) ζ (H.der.norm_mu _ hζ)
  · have h := ((H.splitsC_facts p hp).2 hs).2.2 w (overp w hw)
    exact ⟨h.1, h.2.1⟩
  · have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E)) := by
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 ha
      have h0 : Ideal.Quotient.mk w.asIdeal (p : 𝓞 H.E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (overp w hw)
      have h1 := congrArg (Int.cast : ℤ → 𝓞 H.E ⧸ w.asIdeal) huv
      rw [map_natCast] at h0 ⊢
      push_cast at h1
      rw [h0, mul_zero, add_zero, mul_comm] at h1
      exact IsUnit.of_mul_eq_one _ h1
    exact ⟨hu.unit, rfl, hθ w hw a ha _ rfl⟩
