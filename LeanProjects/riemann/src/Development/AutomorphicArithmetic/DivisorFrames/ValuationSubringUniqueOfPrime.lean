import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

private theorem valuationSubringAtPrime_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (W : ValuationSubring F) (hW : ∀ x : 𝓞 F, (x : F) ∈ W.nonunits ↔ x ∈ v.asIdeal) :
    v.valuationSubringAtPrime F = W := by
  have hmem : ∀ x : 𝓞 F, (x : F) ∈ W := fun x => by
    have hx : IsIntegral W (x : F) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
    rw [← hy]; exact y.2
  haveI : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime F) :=
    Localization.subalgebra.isLocalization_ofField F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (v.valuationSubringAtPrime F) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) v.ne_bot _
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ ?_
  · intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl (⟨x, hx⟩ : v.valuationSubringAtPrime F)
    have hs : ((s : 𝓞 F) : F) ∉ W.nonunits := fun h' => s.2 ((hW _).1 h')
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hs
    have h1 : x * ((s : 𝓞 F) : F) = (a : F) := congrArg Subtype.val h
    have : x = (a : F) * ((s : 𝓞 F) : F)⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ hs.1, mul_one]
    rw [this]; exact W.mul_mem _ _ (hmem a) hs.2
  · intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have := (hW x).2 hx
    rw [ValuationSubring.mem_nonunits_iff_or] at this
    rcases this with h0 | h0
    · exact hx0 (by exact_mod_cast h0)
    · exact h0 (h ▸ ValuationSubring.mem_top _)

theorem UpperTheory.valuationSubring_unique_of_prime :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (W W' : ValuationSubring F), (∀ x : 𝓞 F, (x : F) ∈ W.nonunits ↔ x ∈ v.asIdeal) → (∀ x : 𝓞 F, (x : F) ∈ W'.nonunits ↔ x ∈ v.asIdeal) → W = W' := by
  intro F _ _ v W W' h h'
  exact (valuationSubringAtPrime_eq F v W h).symm.trans (valuationSubringAtPrime_eq F v W' h')
