import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

namespace GlobalTheory.GenSpecialDvr

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coheight_eq_one (B : GlobalTheory.Vert.Model O) (η : B.X) (hη : IsGenSpecial B η) :
    Order.coheight η = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : ϖ ∈ maximalIdeal O := hϖ.not_isUnit
  have hg := B.gen_eq_basicOpen hϖ.ne_zero hm
  obtain ⟨W, hW, h, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := η) trivial
  have : Nonempty W := ⟨⟨η, h⟩⟩
  have : IsNoetherianRing Γ(B.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let a : Γ(B.X, W) := B.X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (B.const ϖ)
  have hD : B.X.basicOpen a = W ⊓ B.gen := by
    rw [hg]; exact Scheme.basicOpen_res _ _ _
  have hin : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ W := fun r => by
    have : hW.fromSpec r ∈ Set.range hW.fromSpec := ⟨r, rfl⟩
    rwa [hW.range_fromSpec] at this
  have key : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ B.gen ↔ a ∉ r.asIdeal := fun r => by
    have h1 : hW.fromSpec r ∈ B.X.basicOpen a ↔ a ∉ r.asIdeal := by
      change r ∈ hW.fromSpec ⁻¹ᵁ B.X.basicOpen a ↔ _
      rw [hW.fromSpec_preimage_basicOpen]
      rfl
    rw [← h1, hD]
    exact ⟨fun h => ⟨hin r, h⟩, fun h => h.2⟩
  let q : PrimeSpectrum Γ(B.X, W) := hW.primeIdealOf ⟨η, h⟩
  have hq : hW.fromSpec q = η := hW.fromSpec_primeIdealOf ⟨η, h⟩
  have haq : a ∈ q.asIdeal := by
    by_contra H
    exact hη.1 (hq ▸ (key q).2 H)
  have ha : a ≠ 0 := fun H => by
    have h0 : genericPoint B.X ∈ W ⊓ B.gen :=
      ⟨((genericPoint_spec B.X).specializes trivial).mem_open W.isOpen h, B.genericPoint_mem_gen⟩
    rw [← hD, H, Scheme.basicOpen_zero] at h0
    exact h0
  have hmin : q.asIdeal ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨q.isPrime, (Ideal.span_singleton_le_iff_mem _).2 haq⟩, fun P hP hle => ?_⟩
    let r : PrimeSpectrum Γ(B.X, W) := ⟨P, hP.1⟩
    have h1 : hW.fromSpec r ∉ B.gen := fun H =>
      (key r).1 H ((Ideal.span_singleton_le_iff_mem _).1 hP.2)
    have h2 : hW.fromSpec r ⤳ hW.fromSpec q :=
      ((PrimeSpectrum.le_iff_specializes r q).1 hle).map hW.fromSpec.continuous
    have h3 : hW.fromSpec r = hW.fromSpec q := (hη.2 _ h1 (hq ▸ h2)).trans hq.symm
    have h4 : r = q := hW.fromSpec.isOpenEmbedding.injective h3
    exact (congrArg PrimeSpectrum.asIdeal h4).ge
  have hle : q.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : q.asIdeal.height ≠ 0 := fun H => by
    have := q.isPrime
    have hb : q.asIdeal = ⊥ := by
      simpa using H
    exact ha (by simpa [hb] using haq)
  have h1 : q.asIdeal.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)
  letI : Algebra Γ(B.X, W) (B.X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk B.X.presheaf (⟨η, h⟩ : W)
  have hl : IsLocalization.AtPrime (B.X.presheaf.stalk η) q.asIdeal :=
    hW.isLocalization_stalk ⟨η, h⟩
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (B.X.presheaf.stalk η)
  rw [ringKrullDim_stalk_eq_coheight, h1] at hd
  exact_mod_cast hd

theorem isDiscreteValuationRing_stalk : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ η : B.X, IsGenSpecial B η → IsDiscreteValuationRing (B.X.presheaf.stalk η) :=
  fun _ _ _ _ B _ η hη =>
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk (coheight_eq_one B η hη)

end GlobalTheory.GenSpecialDvr
