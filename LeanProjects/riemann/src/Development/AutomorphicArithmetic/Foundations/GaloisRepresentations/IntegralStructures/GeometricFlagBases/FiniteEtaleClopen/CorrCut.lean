import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

namespace UpperTheory.Gal.Int.Geo.Cut

theorem corrCut : CorrCut := by
  intro l Y' Y T' j T i s' t' hj hr hcond
  haveI := hj.op
  haveI := hr.op
  have hcl : IsClosed (Set.range i) := by
    rw [hr.rng]
    exact (hj.cl.preimage T.p.continuous).inter (hj.cl.preimage T.r.continuous)
  haveI : IsClosedImmersion i := .of_isPreimmersion _ hcl
  haveI := T.fin
  haveI : IsFinite (s' ≫ j) := by rw [hr.es]; infer_instance
  refine ⟨IsFinite.of_comp s' j, ?_, ?_⟩
  · have hV : j ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) = Y'.basicOpen (l : Γ(Y', ⊤)) := by
      rw [Scheme.Hom.preimage_basicOpen, map_natCast]
      rfl
    let a := (s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ i
    have ha : Set.range a ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hu : s' ((s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι u) ∈ j ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
        rw [hV]
        exact u.2
      change T.p (i ((s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι u)) ∈ Y.basicOpen (l : Γ(Y, ⊤))
      rw [← Scheme.Hom.comp_apply, ← hr.es, Scheme.Hom.comp_apply]
      exact hu
    haveI : Etale (IsOpenImmersion.lift _ a ha ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    haveI : Etale (IsOpenImmersion.lift _ a ha) := Etale.of_comp _ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι
    haveI := T.et
    have e1 : (s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ≫ (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j =
        IsOpenImmersion.lift _ a ha ≫ (T.p ∣_ Y.basicOpen (l : Γ(Y, ⊤))) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [morphismRestrict_ι, ← Category.assoc (IsOpenImmersion.lift _ a ha), IsOpenImmersion.lift_fac,
        ← Category.assoc, morphismRestrict_ι, Category.assoc, hr.es]
      simp only [a, Category.assoc]
    haveI : Etale ((s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ≫ (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j) := by
      rw [e1]
      infer_instance
    exact Etale.of_comp _ ((Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j)
  · intro K _ _ hl y
    rw [← T.deg K hl (y ≫ j)]
    have hbo : ∀ (f : Spec (CommRingCat.of K) ⟶ Y) (u : Spec (CommRingCat.of K)),
        f u ∈ Y.basicOpen (l : Γ(Y, ⊤)) := by
      intro f u
      have htop : f ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) = ⊤ := by
        rw [Scheme.Hom.preimage_basicOpen, map_natCast]
        apply Scheme.basicOpen_of_isUnit
        have hu := (IsUnit.mk0 (l : K) hl).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        rw [map_natCast] at hu
        exact hu
      have hu' : u ∈ f ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
        rw [htop]
        trivial
      exact hu'
    have hw : ∀ w : { z // z ≫ T.p = y ≫ j }, Set.range w.1 ⊆ Set.range i := by
      rintro w _ ⟨u, rfl⟩
      rw [hr.rng]
      have h1 : T.p (w.1 u) = j (y u) := by
        rw [← Scheme.Hom.comp_apply, w.2, Scheme.Hom.comp_apply]
      exact ⟨⟨y u, h1.symm⟩, hcond _ ⟨y u, h1.symm⟩ (hbo (w.1 ≫ T.p) u)⟩
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ i, by rw [Category.assoc, ← hr.es, ← Category.assoc, z.2]⟩
        invFun := fun w => ⟨IsOpenImmersion.lift i w.1 (hw w), by
          rw [← cancel_mono j, Category.assoc, hr.es, ← Category.assoc, IsOpenImmersion.lift_fac, w.2]⟩
        left_inv := fun z => Subtype.ext ((cancel_mono i).mp (IsOpenImmersion.lift_fac _ _ _))
        right_inv := fun w => Subtype.ext (IsOpenImmersion.lift_fac _ _ _) }

end UpperTheory.Gal.Int.Geo.Cut
