import Mathlib

theorem UpperTheory.Reformulated.B.RegularUnitPoints.aux1 :
    ∀ {Ω : Type} [inst : Field Ω],
      @IsLocalRing Ω (@CommSemiring.toSemiring Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst))) := by
  intro Ω inst
  infer_instance

noncomputable def UpperTheory.Reformulated.B.RegularUnitPoints.genPt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          @Quiver.Hom AlgebraicGeometry.Scheme
              (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
              (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X →
            ↥X :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) ↦
      ξ
        (@IsLocalRing.closedPoint Ω (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst))
          (@UpperTheory.Reformulated.B.RegularUnitPoints.aux1 Ω inst))

noncomputable def UpperTheory.Reformulated.B.RegularUnitPoints.Cpt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          @Quiver.Hom AlgebraicGeometry.Scheme
              (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
              (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X →
            Type :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) ↦
      @Subtype ↥X fun (p : ↥X) ↦
        @Specializes (↥X)
          (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
            X.toSheafedSpace)
          (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p

theorem UpperTheory.Reformulated.B.RegularUnitPoints.aux4 :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      (ξ :
        @Quiver.Hom AlgebraicGeometry.Scheme
          (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
            (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
          (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
      (p : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ),
      @Specializes (↥X)
        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
          X.toSheafedSpace)
        (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ)
        (@Subtype.val (↥X)
          (fun (p : ↥X) ↦
            @Specializes (↥X)
              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                X.toSheafedSpace)
              (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
          p) := by
  intro X Ω inst ξ p
  exact p.2

theorem UpperTheory.Reformulated.B.RegularUnitPoints.aux5 :
    ∀ {Ω : Type} [inst : Field Ω],
      @IsLocalRing (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
        (@CommSemiring.toSemiring (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
          (@CommRing.toCommSemiring (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
            (@CommRingCat.instCommRingObjForgetRingHomCarrier (@CommRingCat.of Ω (@Field.toCommRing Ω inst))))) := by
  intro Ω inst
  show IsLocalRing Ω
  infer_instance

noncomputable def UpperTheory.Reformulated.B.RegularUnitPoints.genMap :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            (p : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ) →
              @RingHom
                (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                      (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                          X.toSheafedSpace))
                      (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                          X.toSheafedSpace))
                      (@Subtype.val (↥X)
                        (fun (p : ↥X) ↦
                          @Specializes (↥X)
                            (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                              CommRingCat.instCategory X.toSheafedSpace)
                            (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                        p)) :
                  Type)
                Ω
                (@Semiring.toNonAssocSemiring
                  (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                        CommRingCat.Colimits.hasColimits_commRingCat
                        (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                            X.toSheafedSpace))
                        (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                            X.toSheafedSpace))
                        (@Subtype.val (↥X)
                          (fun (p : ↥X) ↦
                            @Specializes (↥X)
                              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                CommRingCat.instCategory X.toSheafedSpace)
                              (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                          p)) :
                    Type)
                  (@CommSemiring.toSemiring
                    (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                          CommRingCat.Colimits.hasColimits_commRingCat
                          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                            p)) :
                      Type)
                    (@CommRing.toCommSemiring
                      (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                            CommRingCat.Colimits.hasColimits_commRingCat
                            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                                X.toSheafedSpace))
                            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                                X.toSheafedSpace))
                            (@Subtype.val (↥X)
                              (fun (p : ↥X) ↦
                                @Specializes (↥X)
                                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                    CommRingCat.instCategory X.toSheafedSpace)
                                  (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                              p)) :
                        Type)
                      (@CommRingCat.instCommRingObjForgetRingHomCarrier
                        (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                          CommRingCat.Colimits.hasColimits_commRingCat
                          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                            p))))))
                (@Semiring.toNonAssocSemiring Ω
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst)))) :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ) ↦
      @CommRingCat.Hom.hom
        (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
          (@Subtype.val (↥X)
            (fun (p : ↥X) ↦
              @Specializes (↥X)
                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                  X.toSheafedSpace)
                (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
            p))
        (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
        (@CategoryTheory.CategoryStruct.comp CommRingCat
          (@CategoryTheory.Category.toCategoryStruct CommRingCat CommRingCat.instCategory)
          (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@Subtype.val (↥X)
              (fun (p : ↥X) ↦
                @Specializes (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                    X.toSheafedSpace)
                  (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
              p))
          (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ))
          (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
          (@TopCat.Presheaf.stalkSpecializes CommRingCat CommRingCat.instCategory
            CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ)
            (@Subtype.val (↥X)
              (fun (p : ↥X) ↦
                @Specializes (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                    X.toSheafedSpace)
                  (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
              p)
            (@UpperTheory.Reformulated.B.RegularUnitPoints.aux4 X Ω inst ξ p))
          (@AlgebraicGeometry.Scheme.stalkClosedPointTo X (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
            (@UpperTheory.Reformulated.B.RegularUnitPoints.aux5 Ω inst) ξ))

noncomputable def UpperTheory.Reformulated.B.RegularUnitPoints.regAt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ →
              @Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))) :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ) ↦
      @RingHom.range
        (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
              (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
              (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
              (@Subtype.val (↥X)
                (fun (p : ↥X) ↦
                  @Specializes (↥X)
                    (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace)
                    (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                p)) :
          Type)
        Ω
        (@NonAssocCommRing.toNonAssocRing
          (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@Subtype.val (↥X)
                  (fun (p : ↥X) ↦
                    @Specializes (↥X)
                      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                        CommRingCat.instCategory X.toSheafedSpace)
                      (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                  p)) :
            Type)
          (@CommRing.toNonAssocCommRing
            (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                  (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace))
                  (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace))
                  (@Subtype.val (↥X)
                    (fun (p : ↥X) ↦
                      @Specializes (↥X)
                        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                          CommRingCat.instCategory X.toSheafedSpace)
                        (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                    p)) :
              Type)
            (@CommRingCat.instCommRingObjForgetRingHomCarrier
              (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@Subtype.val (↥X)
                  (fun (p : ↥X) ↦
                    @Specializes (↥X)
                      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                        CommRingCat.instCategory X.toSheafedSpace)
                      (@UpperTheory.Reformulated.B.RegularUnitPoints.genPt X Ω inst ξ) p)
                  p)))))
        (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))
        (@UpperTheory.Reformulated.B.RegularUnitPoints.genMap X Ω inst ξ p)

noncomputable def UpperTheory.Reformulated.B.RegularUnitPoints.unitAt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ → Ω → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ) (a : Ω) ↦
      And
        (@Ne Ω a
          (@OfNat.ofNat Ω (nat_lit 0)
            (@Zero.toOfNat0 Ω
              (@MulZeroClass.toZero Ω
                (@instMulZeroClassOfSemiring Ω
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst))))))))
        (And
          (@Membership.mem Ω
            (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
            (@SetLike.instMembership
              (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
              Ω
              (@Subring.instSetLike Ω
                (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))))
            (@UpperTheory.Reformulated.B.RegularUnitPoints.regAt X Ω inst ξ p) a)
          (@Membership.mem Ω
            (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
            (@SetLike.instMembership
              (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
              Ω
              (@Subring.instSetLike Ω
                (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))))
            (@UpperTheory.Reformulated.B.RegularUnitPoints.regAt X Ω inst ξ p)
            (@Inv.inv Ω
              (@InvOneClass.toInv Ω
                (@DivInvOneMonoid.toInvOneClass Ω
                  (@DivisionMonoid.toDivInvOneMonoid Ω
                    (@DivisionCommMonoid.toDivisionMonoid Ω
                      (@CommGroupWithZero.toDivisionCommMonoid Ω
                        (@Semifield.toCommGroupWithZero Ω (@Field.toSemifield Ω inst)))))))
              a)))

noncomputable def UpperTheory.Reformulated.B.RegularUnitPoints.InFibre :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            Nat → @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : Nat) (q : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ) ↦
      Not
        (@UpperTheory.Reformulated.B.RegularUnitPoints.unitAt X Ω inst ξ q
          (@Nat.cast Ω
            (@AddMonoidWithOne.toNatCast Ω
              (@AddGroupWithOne.toAddMonoidWithOne Ω
                (@Ring.toAddGroupWithOne Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst)))))
            p))

theorem UpperTheory.Reformulated.B.RegularUnitPoints.main :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      {ξ :
        @Quiver.Hom AlgebraicGeometry.Scheme
          (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
            (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
          (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X}
      {q : @UpperTheory.Reformulated.B.RegularUnitPoints.Cpt X Ω inst ξ},
      (∀ (r : Nat), Nat.Prime r → Not (@UpperTheory.Reformulated.B.RegularUnitPoints.InFibre X Ω inst ξ r q)) →
        ∀ (n : Nat),
          @Ne Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @UpperTheory.Reformulated.B.RegularUnitPoints.unitAt X Ω inst ξ q
              (@Nat.cast Ω
                (@AddMonoidWithOne.toNatCast Ω
                  (@AddGroupWithOne.toAddMonoidWithOne Ω
                    (@Ring.toAddGroupWithOne Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst)))))
                n) := by
  intro X Ω inst ξ q hq n hn
  have key : ∀ m : ℕ, m ≠ 0 → UpperTheory.Reformulated.B.RegularUnitPoints.unitAt ξ q (m : Ω) := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _
      refine ⟨by simp, ?_, ?_⟩
      · simp [(UpperTheory.Reformulated.B.RegularUnitPoints.regAt ξ q).one_mem]
      · simp [(UpperTheory.Reformulated.B.RegularUnitPoints.regAt ξ q).one_mem]
    | prime p hp =>
      intro _
      have := hq p hp
      unfold UpperTheory.Reformulated.B.RegularUnitPoints.InFibre at this
      exact not_not.mp this
    | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := by rintro rfl; simp at hab
      have hb0 : b ≠ 0 := by rintro rfl; simp at hab
      obtain ⟨a1, a2, a3⟩ := ha ha0
      obtain ⟨b1, b2, b3⟩ := hb hb0
      refine ⟨?_, ?_, ?_⟩
      · push_cast; exact mul_ne_zero a1 b1
      · push_cast; exact Subring.mul_mem _ a2 b2
      · push_cast; rw [mul_inv]; exact Subring.mul_mem _ a3 b3
  exact key n hn
