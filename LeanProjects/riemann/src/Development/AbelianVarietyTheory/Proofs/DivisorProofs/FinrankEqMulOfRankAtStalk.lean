import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.FinrankComp

theorem finrank_eq_mul_of_rankAtStalk (K S T : Type*) [Field K] [CommRing S] [AddCommGroup T]
    [Algebra K S] [Module S T] [Module K T] [IsScalarTower K S T] [Module.Finite K S]
    [Module.Finite S T] [Module.Flat S T] (d : ℕ)
    (h : ∀ p : PrimeSpectrum S, Module.rankAtStalk T p = d) :
    Module.finrank K T = d * Module.finrank K S := by
  have : IsArtinianRing S := IsArtinianRing.of_finite K S
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq S T d
    (fun P => by
      have := P.isMaximal
      letI := Ideal.Quotient.field P.asIdeal
      have h1 := Module.rankAtStalk_baseChange (R := S) (M := T) (S := S ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, h] at h1
      exact h1)
  rw [(b.equivFun.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_comp_field {X Y : Scheme.{0}} (K : CommRingCat.{0}) (hK : IsField K)
    (φ : X ⟶ Y) (ψ : Y ⟶ Spec K) [IsFinite φ] [Flat φ] [IsFinite ψ] [Flat ψ] (d : ℕ)
    (h : ∀ y, φ.finrank y = d) (z : Spec K) : (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · have _ : IsAffine Y := isAffine_of_isAffineHom ψ
    have := this (φ ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ ψ) (fun y => by
      rw [← h (Y.isoSpec.inv y)]
      exact Scheme.Hom.finrank_of_isPullback (𝟙 X) _ φ Y.isoSpec.inv
        (IsPullback.of_horiz_isIso ⟨by simp⟩) y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ T, X = Spec T generalizing X
  · have _ : IsAffine X := isAffine_of_isAffineHom φ
    have := this (X.isoSpec.inv ≫ φ) (fun y => by simpa using h y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective ψ
  obtain ⟨g, rfl⟩ := Spec.map_surjective φ
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rename_i hf1 hf2 hg1 hg2
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank (f := f ≫ g) (hg1.comp hf1) (hf2.comp hg2),
    Scheme.Hom.finrank_SpecMap_eq_finrank hf1 hf2]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hg1 hg2] at h
  letI := hK.toField
  algebraize [f.hom, g.hom, (f ≫ g).hom]
  rw [← RingHom.algebraMap_toAlgebra g.hom, RingHom.finrank_algebraMap] at h
  rw [← RingHom.algebraMap_toAlgebra f.hom, ← RingHom.algebraMap_toAlgebra (f ≫ g).hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]
  have : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq' rfl
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  exact finrank_eq_mul_of_rankAtStalk K S T d h

theorem finrank_comp_of_const {X Y Z : Scheme.{0}} (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsFinite φ] [Flat φ]
    [IsFinite ψ] [Flat ψ] (d : ℕ) (h : ∀ y, φ.finrank y = d) (z : Z) :
    (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  let i := Z.fromSpecResidueField z
  let pt : Spec (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  have hz : i pt = z := Scheme.fromSpecResidueField_apply z pt
  have hp := (IsPullback.of_hasPullback φ (pullback.fst ψ i)).paste_vert
    (IsPullback.of_hasPullback ψ i)
  rw [← hz, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp pt,
    ← Scheme.Hom.finrank_pullback_snd ψ i pt]
  exact finrank_comp_field _ (Field.toIsField _) _ _ d
    (fun y => by rw [Scheme.Hom.finrank_pullback_snd, h]) pt

theorem finrank_comp : ∀ {X Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsFinite φ] [Flat φ] [IsFinite ψ] [Flat ψ] (d e : ℕ), (∀ y, φ.finrank y = d) → (∀ z, ψ.finrank z = e) → ∀ z, (φ ≫ ψ).finrank z = d * e := by
  intro X Y Z _ _ φ ψ _ _ _ _ d e hd he z
  rw [finrank_comp_of_const φ ψ d hd z, he]

end GlobalTheory.FinrankComp
