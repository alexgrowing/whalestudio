import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits

namespace GlobalTheory.RegCoverToIntegers

theorem residueDegree_fst_ne_zero {X Y₁ Y₂ : Scheme.{0}} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (z : ↥(pullback f g))
    (h : g.residueDegree (pullback.snd f g z) ≠ 0) : (pullback.fst f g).residueDegree z ≠ 0 := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  have hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite g _).1 h).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  let s : PrimeSpectrum T.tensor := Scheme.Pullback.SpecOfPoint z
  have hs : T.SpecTensorTo s = z := Scheme.Pullback.SpecTensorTo_SpecOfPoint z
  have hm : s.asIdeal.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' T.tensorInl.hom hl.to_isIntegral s.asIdeal ?_
    have hp : (s.asIdeal.comap T.tensorInl.hom).IsPrime := inferInstance
    rw [Ideal.eq_bot_of_prime (s.asIdeal.comap T.tensorInl.hom)]
    exact Ideal.bot_isMaximal
  letI := Ideal.Quotient.field s.asIdeal
  let ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ s.asIdeal) := CommRingCat.ofHom (Ideal.Quotient.mk s.asIdeal)
  have hρ : ρ.hom.Finite := RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let q : Spec (CommRingCat.of (T.tensor ⧸ s.asIdeal)) := (⊥ : PrimeSpectrum (T.tensor ⧸ s.asIdeal))
  have hq : Spec.map ρ q = s := PrimeSpectrum.ext Ideal.mk_ker
  have e : (Spec.map ρ ≫ T.SpecTensorTo) q = z := by
    rw [Scheme.Hom.comp_apply, hq, hs]
  rw [← e]
  refine PullbackFinitePoint.residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q
  rw [Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]

theorem charZero_residueField_genericPoint (Y : Scheme.{0}) [IsIntegral Y] (hc : CharZero Γ(Y, ⊤)) :
    CharZero (Y.residueField (genericPoint Y)) := by
  have h₁ : CharZero Y.functionField := charZero_of_injective_ringHom
    (f := (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) (germ_injective_of_isIntegral _ _ _)
  let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue (genericPoint Y)).hom
  exact charZero_of_injective_ringHom f.injective

end GlobalTheory.RegCoverToIntegers

namespace GlobalTheory.RegCoverToIntegers

theorem exists_regCover_toIntegers : GlobalTheory.Published.RegularAlteration → ∀ (K : Type) [Field K] [NumberField K] (k : Type)
    [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsArithVar p 1 →
    ∃ C : RegCover p, Nonempty (C.Y ⟶ Sp (𝓞 K)) := by
  intro hRA K _ _ k _ S p _ h
  let t : S ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  let u : Sp (𝓞 K) ⟶ Sp ℤ := spMap (Int.castRingHom (𝓞 K))
  have hfin : (Int.castRingHom (𝓞 K)).Finite := RingHom.finite_algebraMap.2 inferInstance
  have : IsFinite u := (IsFinite.SpecMap_iff _).2 hfin
  obtain ⟨y, hy⟩ : ∃ y : Sp (𝓞 K), u y = t (genericPoint S) := by
    obtain ⟨y, hy⟩ := RingHom.IsIntegral.comap_surjective (f := Int.castRingHom (𝓞 K)) hfin.to_isIntegral
      Int.cast_injective (t (genericPoint S))
    exact ⟨y, hy⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := u) _ _ hy.symm
  have hz : (pullback.fst t u).residueDegree z ≠ 0 := by
    refine residueDegree_fst_ne_zero t u z ?_
    exact (PullbackFinitePoint.residueDegree_ne_zero_iff_finite u _).2
      (residueFieldMap_finite_of_locallyQuasiFinite u _)
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint z
  let g : Z ⟶ S := i ≫ pullback.fst t u
  have : IsFinite g := inferInstance
  have gen : g (genericPoint Z) = genericPoint S := by
    simp [g, hi, hz₁]
  have deg : g.residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact hz
  have hP : IsProjOver (g ≫ p) := GlobalTheory.isProjOver_comp_of_isFinite g h.isProjOver
  have hfl : Flat ((g ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have c₁ : CharZero Γ(S, ⊤) := h.charZero
    have c₂ := charZero_residueField_genericPoint S c₁
    have c₃ : CharZero (Z.residueField (genericPoint Z)) := by
      have : ∀ s : S, s = genericPoint S → CharZero (S.residueField s) := by
        rintro _ rfl; exact c₂
      have := this _ gen
      exact (RingHom.charZero_iff (Scheme.Hom.residueFieldMap _ _).hom.injective).1 this
    exact (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (g ≫ p) 1 :=
    ⟨h.isDomain, h.finite, inferInstance, hP, hfl,
      DimCover.topologicalKrullDim_eq k S Z p (g ≫ p) 1 h hP hfl g rfl gen deg⟩
  obtain ⟨D⟩ := RegCoverExists.nonempty_regCover hRA k Z (g ≫ p) hZ
  refine ⟨⟨D.Y, D.ρ ≫ g, ?_, ?_, ?_⟩, ⟨D.ρ ≫ i ≫ pullback.snd t u⟩⟩
  · simpa [Category.assoc] using D.reg
  · simp only [Scheme.Hom.comp_apply]
    rw [D.generic, gen]
  · rw [CurveDegreesCompare.residueDegree_comp, D.generic]
    exact mul_ne_zero deg D.finite

end GlobalTheory.RegCoverToIntegers
