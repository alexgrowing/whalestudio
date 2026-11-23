import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.PullbackGenericTensor

theorem isField_of_surjective {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) (hA : IsField A) : IsField B := by
  refine ⟨exists_pair_ne B, mul_comm, fun {a} ha => ?_⟩
  obtain ⟨b, rfl⟩ := hφ a
  have hb : b ≠ 0 := fun h => ha (by rw [h, map_zero])
  obtain ⟨c, hc⟩ := hA.mul_inv_cancel hb
  exact ⟨φ c, by rw [← map_mul, hc, map_one]⟩

theorem isField_tensor :
    (∀ (R : CommRingCat.{0}) (q : Spec R), (∀ q' : Spec R, q' = q) → IsField ((Spec R).presheaf.stalk q) → IsField R) →
    ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral (Limits.pullback f g)],
    IsPreimmersion (Scheme.Pullback.Triplet.ofPoint (genericPoint (Limits.pullback f g : Scheme.{0}))).SpecTensorTo →
    g.residueDegree (Limits.pullback.snd f g (genericPoint (Limits.pullback f g : Scheme.{0}))) ≠ 0 →
    IsField (Scheme.Pullback.Triplet.ofPoint (genericPoint (Limits.pullback f g : Scheme.{0}))).tensor := by
  intro H X Y S f g _ hpre hdeg
  set η : ↥(Limits.pullback f g) := genericPoint (Limits.pullback f g : Scheme.{0}) with hη
  set T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint η with hT
  have hg : ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite g _).1 hdeg).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (S.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  have hmax : ∀ p : PrimeSpectrum T.tensor, p.asIdeal.IsMaximal := by
    intro p
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' T.tensorInl.hom hl.to_isIntegral p.asIdeal ?_
    have hp : (p.asIdeal.comap T.tensorInl.hom).IsPrime := inferInstance
    rw [Ideal.eq_bot_of_prime (p.asIdeal.comap T.tensorInl.hom)]
    exact Ideal.bot_isMaximal
  let q : Spec T.tensor := Scheme.Pullback.SpecOfPoint η
  have hs : T.SpecTensorTo q = η := Scheme.Pullback.SpecTensorTo_SpecOfPoint η
  have hq : ∀ q' : Spec T.tensor, q' = q := by
    intro q'
    have h1 : T.SpecTensorTo q ⤳ T.SpecTensorTo q' := hs ▸ genericPoint_specializes _
    have h2 : q ⤳ q' := (T.SpecTensorTo.isEmbedding.isInducing.specializes_iff).1 h1
    have h3 : (q : PrimeSpectrum T.tensor).asIdeal ≤ (q' : PrimeSpectrum T.tensor).asIdeal :=
      (PrimeSpectrum.le_iff_specializes (q : PrimeSpectrum T.tensor) q').2 h2
    exact (PrimeSpectrum.ext ((hmax q).eq_of_le (q' : PrimeSpectrum T.tensor).isPrime.ne_top h3)).symm
  have hη' : IsField ((Limits.pullback f g : Scheme.{0}).presheaf.stalk (T.SpecTensorTo q)) := by
    rw [hs]
    exact Field.toIsField (Limits.pullback f g : Scheme.{0}).functionField
  exact H T.tensor q hq (isField_of_surjective _ (T.SpecTensorTo.stalkMap_surjective q) hη')

end GlobalTheory.PullbackGenericTensor
