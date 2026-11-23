import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.AffineCurveSum

theorem length_quot_eq {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (p : Submonoid B)
    [IsLocalization p S] (b : B) :
    Module.length S (S ⧸ Ideal.span {algebraMap B S b}) =
      Module.length (Localization p) (LocalizedModule p (B ⧸ Ideal.span {b})) := by
  let e := IsLocalization.algEquiv p (Localization p) S
  let : Algebra (Localization p) S := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower B (Localization p) S := .of_algebraMap_eq fun x => (e.commutes x).symm
  have h : Submodule.localized' S p (Algebra.linearMap B S) (Ideal.span {b}) =
      Ideal.span {algebraMap B S b} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [← h, ← Module.length_eq_of_surjective (S := Localization p) (R := S) e.surjective]
  exact (((IsLocalizedModule.iso p (Submodule.toLocalizedQuotient' S p (Algebra.linearMap B S)
    (Ideal.span {b}))).extendScalarsOfIsLocalization p (Localization p)).length_eq).symm

theorem finsum_ord_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), b ≠ 0 → ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ m : MaximalSpectrum Γ(Y, ⊤), ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl (Γ(Y, ⊤) ⧸ Ideal.span {b}))).toNat : ℝ) * Real.log (Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal)) := by
  intro k _ Y _ _ _ q hq b hb
  have hU := isAffineOpen_top Y
  have hd : ringKrullDim Γ(Y, ⊤) = 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have := (Scheme.homeoOfIso Y.isoSpec).isHomeomorph.topologicalKrullDim_eq
    exact this.symm.trans (hq.dim_eq.trans (by simp))
  have hc (z : Y) : (Order.coheight z : WithBot ℕ∞) =
      (hU.primeIdealOf ⟨z, trivial⟩).asIdeal.height := by
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨z, trivial⟩ : (⊤ : Y.Opens))
    have := hU.isLocalization_stalk ⟨z, trivial⟩
    exact (ringKrullDim_stalk_eq_coheight z).symm.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)
  have hK : Ring.KrullDimLE 1 Γ(Y, ⊤) := Ring.krullDimLE_iff.2 (by simp [hd])
  have hmax (P : PrimeSpectrum Γ(Y, ⊤)) : P.asIdeal.height = 1 ↔ P.asIdeal.IsMaximal := by
    constructor
    · intro h
      refine Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hK _ (fun h0 => ?_) P.isPrime
      rw [h0, Ideal.height_bot] at h
      exact zero_ne_one h
    · intro h
      have h1 : P.asIdeal.height ≤ 1 := by
        have := (Ideal.height_le_ringKrullDim_of_ne_top h.ne_top).trans_eq hd
        exact_mod_cast this
      refine le_antisymm h1 (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
      have h2 : P.asIdeal = ⊥ := by
        simpa [IsDomain.minimalPrimes_eq_singleton_bot] using Ideal.height_eq_zero_iff.1 h0
      have h3 : IsField Γ(Y, ⊤) := Ring.isField_iff_maximal_bot.2 (h2 ▸ h)
      rw [ringKrullDim_eq_zero_of_isField h3] at hd
      exact zero_ne_one hd
  let i : MaximalSpectrum Γ(Y, ⊤) → Y := fun m => hU.fromSpec m.toPrimeSpectrum
  have hi : Function.Injective i :=
    hU.fromSpec.isOpenEmbedding.injective.comp (MaximalSpectrum.toPrimeSpectrum_injective)
  have hp (m) : hU.primeIdealOf ⟨i m, trivial⟩ = m.toPrimeSpectrum :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq' _ (Set.range i) Set.univ ?_, finsum_mem_range hi]
  · refine finsum_congr fun m => ?_
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨i m, trivial⟩ : (⊤ : Y.Opens))
    have hl : IsLocalization.AtPrime (Y.presheaf.stalk (i m)) m.asIdeal := by
      have := hU.isLocalization_stalk ⟨i m, trivial⟩
      convert this
      exact congrArg PrimeSpectrum.asIdeal (hp m).symm
    have h1 : Order.coheight (i m) = 1 := by
      have := hc (i m)
      rw [hp, (hmax _).2 m.isMaximal] at this
      exact_mod_cast this
    have hb' : algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective _ m.asIdeal.primeCompl_le_nonZeroDivisors)).2 hb
    have h2 := ord_algebraMap h1 hb'
    rw [length_quot_eq m.asIdeal.primeCompl] at h2
    have h3 : algebraMap Γ(Y, ⊤) Y.functionField b =
        algebraMap _ Y.functionField (algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b) :=
      (algebraMap_germ (Opens.mem_top (i m)) b).symm
    have h4 : Nat.card (Y.residueField (i m)) = Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal) :=
      Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m.asIdeal
        (Y.presheaf.stalk (i m))).symm.toEquiv
    rw [h3, h2, h4, Int.cast_natCast]
  · intro z hz
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have h1 : Order.coheight z = 1 := by
      by_contra h
      exact hz (by simp [Scheme.ord_eq_zero_of_coheight_neq_one h])
    have h2 := hc z
    rw [h1] at h2
    exact ⟨⟨_, (hmax (hU.primeIdealOf ⟨z, trivial⟩)).1 (by exact_mod_cast h2.symm)⟩,
      hU.fromSpec_primeIdealOf ⟨z, trivial⟩⟩

end GlobalTheory.AffineCurveSum
