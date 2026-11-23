import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

open AlgebraicGeometry CategoryTheory in
private lemma UpperTheory.Reformulated.B.RangeExtension.ext_aux {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {A B : CommRingCat.{0}} (i : A ⟶ B) (hi : Function.Injective i.hom)
    (a b : Spec A ⟶ X) (ha : ∀ z, a z ∈ U) (hb : ∀ z, b z ∈ U)
    (h : Spec.map i ≫ a = Spec.map i ≫ b) : a = b := by
  haveI : IsAffine U.toScheme := hU
  have hr : ∀ c : Spec A ⟶ X, (∀ z, c z ∈ U) → Set.range c ⊆ Set.range U.ι := by
    intro c hc
    rintro _ ⟨z, rfl⟩
    simpa using hc z
  let a' := IsOpenImmersion.lift U.ι a (hr a ha)
  let b' := IsOpenImmersion.lift U.ι b (hr b hb)
  have ha' : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hb' : b' ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h' : Spec.map i ≫ a' = Spec.map i ≫ b' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ha', hb', h]
  let s := Spec.preimage (a' ≫ U.toScheme.isoSpec.hom)
  let t := Spec.preimage (b' ≫ U.toScheme.isoSpec.hom)
  have hs : Spec.map s = a' ≫ U.toScheme.isoSpec.hom := Spec.map_preimage _
  have ht : Spec.map t = b' ≫ U.toScheme.isoSpec.hom := Spec.map_preimage _
  have h2 : s ≫ i = t ≫ i := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hs, ht, ← Category.assoc, ← Category.assoc, h']
  have hm : Mono i := ConcreteCategory.mono_of_injective i hi
  have h3 : s = t := (cancel_mono i).1 h2
  have h4 : a' = b' := by
    rw [← cancel_mono U.toScheme.isoSpec.hom, ← hs, ← ht, h3]
  rw [← ha', ← hb', h4]

open AlgebraicGeometry CategoryTheory in
private lemma UpperTheory.Reformulated.B.RangeExtension.finiteRing_sq_sub_mul_sq_eq_of_card {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) {R : Type} [CommRing R] (φ : R →+* Ω)
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ)
    (hxU : ∀ z, x z ∈ U) (p : X) (hp : ξ (IsLocalRing.closedPoint Ω) ⤳ p) (hpU : p ∈ U)
    (hinj : Function.Injective
      (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ).hom)
    (hreg : ∀ a, φ a ∈ (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ).hom.range) :
    p ∈ Set.range x := by
  have hi1 : Spec.map (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ) ≫
      X.fromSpecStalk p = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  generalize X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ = i at hinj hreg hi1
  let e : X.presheaf.stalk p ≃+* i.hom.range :=
    RingEquiv.ofBijective i.hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ X.presheaf.stalk p, g ≫ i = CommRingCat.ofHom φ := by
    refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict i.hom.range hreg)), ?_⟩
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict i.hom.range hreg a))
  have hi2 : Spec.map i ≫ Spec.map g ≫ x = ξ := by
    rw [← Spec.map_comp_assoc, hg]
    exact hx
  have key : Spec.map g ≫ x = X.fromSpecStalk p := by
    refine UpperTheory.Reformulated.B.RangeExtension.ext_aux hU i hinj _ _ ?_ ?_ (hi2.trans hi1.symm)
    · intro z
      simpa using hxU _
    · intro z
      have hz : X.fromSpecStalk p z ∈ Set.range (X.fromSpecStalk p) := ⟨z, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hz
      exact Specializes.mem_open hz U.2 hpU
  have hmem : p ∈ Set.range (X.fromSpecStalk p) := ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← key] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨Spec.map g z, by rw [← Scheme.Hom.comp_apply]; exact hz⟩

theorem UpperTheory.Reformulated.B.RangeExtension.mem_range :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      {ξ :
        @Quiver.Hom AlgebraicGeometry.Scheme
          (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
            (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
          (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X},
      @GlobalTheory.CompanionTheory.Ar.IsCptGen X Ω inst ξ →
        ∀ {U : X.Opens},
          @AlgebraicGeometry.IsAffineOpen X U →
            ∀ {R : Type} [inst_1 : CommRing R]
              (φ :
                @RingHom R Ω
                  (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                  (@Semiring.toNonAssocSemiring Ω
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst)))))
              (x :
                @Quiver.Hom AlgebraicGeometry.Scheme
                  (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                    (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                  (AlgebraicGeometry.Spec (@CommRingCat.of R inst_1)) X),
              @Eq
                  (@Quiver.Hom AlgebraicGeometry.Scheme
                    (@CategoryTheory.CategoryStruct.toQuiver AlgebraicGeometry.Scheme
                      (@CategoryTheory.Category.toCategoryStruct AlgebraicGeometry.Scheme
                        AlgebraicGeometry.Scheme.instCategory))
                    (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω (@Field.toCommRing Ω inst)) X)
                  (@CategoryTheory.CategoryStruct.comp AlgebraicGeometry.Scheme
                    (@CategoryTheory.Category.toCategoryStruct AlgebraicGeometry.Scheme
                      AlgebraicGeometry.Scheme.instCategory)
                    (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω (@Field.toCommRing Ω inst)) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R inst_1) X
                    (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R Ω inst_1 (@Field.toCommRing Ω inst) φ) x)
                  ξ →
                (∀ (z : ↥(AlgebraicGeometry.Spec (@CommRingCat.of R inst_1))),
                    @Membership.mem (↥X) X.Opens
                      (@SetLike.instMembership X.Opens (↥X)
                        (@TopologicalSpace.Opens.instSetLike (↥X)
                          (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                            CommRingCat.instCategory X.toSheafedSpace)))
                      U (x z)) →
                  ∀ (q : @GlobalTheory.CompanionTheory.Ar.Cpt X Ω inst ξ),
                    @Membership.mem (↥X) X.Opens
                        (@SetLike.instMembership X.Opens (↥X)
                          (@TopologicalSpace.Opens.instSetLike (↥X)
                            (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                              CommRingCat.instCategory X.toSheafedSpace)))
                        U
                        (@Subtype.val (↥X)
                          (fun (p : ↥X) ↦
                            @Specializes (↥X)
                              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                CommRingCat.instCategory X.toSheafedSpace)
                              (@GlobalTheory.CompanionTheory.Ar.genPt X Ω inst ξ) p)
                          q) →
                      (∀ (a : R),
                          @Membership.mem Ω
                            (@Subring Ω
                              (@NonAssocCommRing.toNonAssocRing Ω
                                (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
                            (@SetLike.instMembership
                              (@Subring Ω
                                (@NonAssocCommRing.toNonAssocRing Ω
                                  (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
                              Ω
                              (@Subring.instSetLike Ω
                                (@NonAssocCommRing.toNonAssocRing Ω
                                  (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))))
                            (@GlobalTheory.CompanionTheory.Ar.regAt X Ω inst ξ q)
                            (@DFunLike.coe
                              (@RingHom R Ω
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                                (@Semiring.toNonAssocSemiring Ω
                                  (@DivisionSemiring.toSemiring Ω
                                    (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst)))))
                              R (fun (x : R) ↦ Ω)
                              (@RingHom.instFunLike R Ω
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                                (@Semiring.toNonAssocSemiring Ω
                                  (@DivisionSemiring.toSemiring Ω
                                    (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst)))))
                              φ a)) →
                        @Membership.mem (↥X) (Set ↥X) (@Set.instMembership ↥X)
                          (@Set.range ↥X ↥(AlgebraicGeometry.Spec (@CommRingCat.of R inst_1)) ⇑x)
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@GlobalTheory.CompanionTheory.Ar.genPt X Ω inst ξ) p)
                            q) := by
  intro X Ω _ ξ hξ U hU R _ φ x hx hxU q hqU hreg
  exact UpperTheory.Reformulated.B.RangeExtension.finiteRing_sq_sub_mul_sq_eq_of_card hU φ x hx hxU q.1 q.2 hqU (hξ.inj q) hreg
