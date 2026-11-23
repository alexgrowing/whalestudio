import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.StabFlat

theorem eq_ker_stalkMap_of_points {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (h : H)
    (I : Ideal (X.presheaf.stalk (j h)))
    (hI : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔
        I ≤ RingHom.ker φ) : I = RingHom.ker (j.stalkMap h).hom := by
  have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
    (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
      ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
  have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
  have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : y (IsLocalRing.closedPoint _) = h := by
    apply j.isClosedEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
    exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
  have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
  refine le_antisymm h₁ fun a ha => Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [← hψ', RingHom.mem_ker.1 ha, map_zero]

theorem flat_of_isFinite_of_ideals : ∀ (V : Type) [CommRing V] [IsLocalRing V] (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → IsFinite (j ≫ f) → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → ∃ I : Ideal (X.presheaf.stalk (j h)), ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ X H f j hj hfin hI
  refine Flat.of_stalkMap _ fun h' => ?_
  obtain ⟨h, hh, hc⟩ : ∃ h : H, h' ⤳ h ∧ (j ≫ f) h = IsLocalRing.closedPoint V := by
    have hcl : IsClosed ((j ≫ f) '' closure {h'}) := (j ≫ f).isClosedMap _ isClosed_closure
    have hm : IsLocalRing.closedPoint V ∈ (j ≫ f) '' closure {h'} :=
      (IsLocalRing.specializes_closedPoint ((j ≫ f) h')).mem_closed hcl ⟨h', subset_closure rfl, rfl⟩
    obtain ⟨h, hh, e⟩ := hm
    exact ⟨h, specializes_iff_mem_closure.2 hh, e⟩
  refine UnramifiedEndFlat.flat_stalkMap_of_specializes _ hh ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have hloc : IsLocalHom σ.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint σ.hom).2 ?_
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ).trans ?_
    exact (congrArg f Scheme.fromSpecStalk_closedPoint).trans hc
  obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hloc
  obtain rfl := eq_ker_stalkMap_of_points j h I hI
  have fl : (σ ≫ j.stalkMap h).hom.Flat :=
    hr.comp (RingHom.Flat.of_bijective
      (f := (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective h)).toRingHom)
      (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective h)).bijective)
  have e : σ ≫ j.stalkMap h = StructureSheaf.toStalk V ((j ≫ f) h) ≫ (j ≫ f).stalkMap h := by
    apply Spec.map_injective
    refine Eq.trans ?_ (Spec.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Spec.fromSpecStalk_eq' (CommRingCat.of V) ((j ≫ f) h)))
    rw [Spec.map_comp, hσ, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (j ≫ f)).symm
  let S := (Spec (CommRingCat.of V)).presheaf.stalk ((j ≫ f) h)
  letI : Algebra V S := StructureSheaf.stalkAlgebra V ((j ≫ f) h)
  have : ((j ≫ f) h).asIdeal.IsPrime := PrimeSpectrum.isPrime (R := V) _
  have : IsLocalization.AtPrime S ((j ≫ f) h).asIdeal := StructureSheaf.IsLocalization.to_stalk V _
  letI : Algebra V (H.presheaf.stalk h) := (σ ≫ j.stalkMap h).hom.toAlgebra
  letI : Algebra S (H.presheaf.stalk h) := ((j ≫ f).stalkMap h).hom.toAlgebra
  have : IsScalarTower V S (H.presheaf.stalk h) := IsScalarTower.of_algebraMap_eq' (congrArg (·.hom) e)
  exact (Module.flat_iff_of_isLocalization S ((j ≫ f) h).asIdeal.primeCompl (H.presheaf.stalk h)).2 fl

end GlobalTheory.StabFlat
