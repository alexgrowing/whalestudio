import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem isDominant_generic_stalk (X : Scheme.{0}) (x : X) [IsDomain (X.presheaf.stalk x)] (V O : X.Opens) (hx : x ∈ V)
    (hV : IsIntegral V.toScheme) (hOV : O ≤ V) (ι : Sp (FractionRing (X.presheaf.stalk x)) ⟶ O.toScheme)
    (hι : ι ≫ O.ι = jK (X.presheaf.stalk x) ≫ X.fromSpecStalk x) : IsDominant ι := by
  obtain ⟨t⟩ : Nonempty (Sp (FractionRing (X.presheaf.stalk x))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing (X.presheaf.stalk x))))
  have hbot : ∀ q : Spec (CommRingCat.of (X.presheaf.stalk x)), jK (X.presheaf.stalk x) t ⤳ q := by
    intro q
    refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
    have ht : (t : PrimeSpectrum (FractionRing (X.presheaf.stalk x))).asIdeal = ⊥ := by
      have := (t : PrimeSpectrum (FractionRing (X.presheaf.stalk x))).isPrime
      exact Ideal.eq_bot_of_prime _
    have hc : (jK (X.presheaf.stalk x) t : PrimeSpectrum (X.presheaf.stalk x)).asIdeal = ⊥ := by
      change Ideal.comap (algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))
        (t : PrimeSpectrum (FractionRing (X.presheaf.stalk x))).asIdeal = ⊥
      rw [ht]
      exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)
    change (jK (X.presheaf.stalk x) t : PrimeSpectrum (X.presheaf.stalk x)).asIdeal ≤ _
    rw [hc]
    exact bot_le
  set z : X := X.fromSpecStalk x (jK (X.presheaf.stalk x) t) with hz
  have hzw : ∀ w : X, w ⤳ x → z ⤳ w := by
    intro w hw
    obtain ⟨q, rfl⟩ : w ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]; exact hw
    exact (hbot q).map (X.fromSpecStalk x).continuous
  have hzO : O.ι (ι t) = z := by
    have := congrArg (fun g => g t) hι
    simpa using this
  let w₀ : V.toScheme := genericPoint V.toScheme
  have hw₀ : IsGenericPoint w₀ (⊤ : Set V.toScheme) := genericPoint_spec V.toScheme
  have h₁ : w₀ ⤳ (⟨x, hx⟩ : V.toScheme) := genericPoint_specializes _
  have h₂ : z ⤳ V.ι w₀ := hzw _ (h₁.map V.ι.continuous)
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_inter_open]
  rintro S hS ⟨o, ho⟩
  have hS' : IsOpen (O.ι '' S) := O.ι.isOpenEmbedding.isOpenMap S hS
  have hP : IsOpen (V.ι ⁻¹' (O.ι '' S)) := hS'.preimage V.ι.continuous
  have hoV : O.ι o ∈ V := hOV o.2
  have hne : ((⊤ : Set V.toScheme) ∩ (V.ι ⁻¹' (O.ι '' S))).Nonempty :=
    ⟨⟨O.ι o, hoV⟩, trivial, o, ho, rfl⟩
  have hmem : w₀ ∈ V.ι ⁻¹' (O.ι '' S) := (hw₀.mem_open_set_iff hP).mpr hne
  have hzS : z ∈ O.ι '' S := h₂.mem_open hS' hmem
  obtain ⟨s, hs, hsz⟩ := hzS
  have : s = ι t := O.ι.isOpenEmbedding.injective (hsz.trans hzO.symm)
  exact ⟨ι t, this ▸ hs, Set.mem_range_self t⟩

theorem isDominant_fractionRing_stalk : ∀ (X : Scheme.{0}) (x : X) [IsDomain (X.presheaf.stalk x)] (V O : X.Opens), x ∈ V →
    IsIntegral V.toScheme → O ≤ V → ∀ ι : Sp (FractionRing (X.presheaf.stalk x)) ⟶ O.toScheme,
    ι ≫ O.ι = jK (X.presheaf.stalk x) ≫ X.fromSpecStalk x → IsDominant ι :=
  fun X x _ V O hx hV hOV ι hι => isDominant_generic_stalk X x V O hx hV hOV ι hι

end GlobalTheory
