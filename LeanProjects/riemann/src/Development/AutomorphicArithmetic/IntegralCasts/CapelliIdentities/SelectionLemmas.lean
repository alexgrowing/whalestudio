import Mathlib

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux1.{u_1} :
    ∀ {K : Type u_1} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))) := by
  intros; infer_instance

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux2.{u_1} :
    ∀ {K : Type u_1} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))) := by
  intros; infer_instance

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux3.{u_1, u_2, u_3} :
    ∀ {S : Type u_3} {K : Type u_2} {V : Type u_1} [inst : CommRing S] [inst_1 : Field K]
      [inst_2 :
        @Algebra S K (@CommRing.toCommSemiring S inst)
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
      [inst_3 : AddCommGroup V]
      [inst_4 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
          (@AddCommGroup.toAddCommMonoid V inst_3)]
      [inst_5 :
        @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
          (@AddCommGroup.toAddCommMonoid V inst_3)]
      [@IsScalarTower S K V
          (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_2)
          (@SMulZeroClass.toSMul K V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))))
            (@DistribSMul.toSMulZeroClass K V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))
              (@DistribMulAction.toDistribSMul K V
                (@Semiring.toMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3)))
                (@Module.toDistribMulAction K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@AddCommGroup.toAddCommMonoid V inst_3) inst_4))))
          (@SMulZeroClass.toSMul S V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))))
            (@DistribSMul.toSMulZeroClass S V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))
              (@DistribMulAction.toDistribSMul S V
                (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3)))
                (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                  (@AddCommGroup.toAddCommMonoid V inst_3) inst_5))))],
      @LinearMap.CompatibleSMul V K (@AddCommGroup.toAddCommMonoid V inst_3)
        (@Semiring.toAddCommMonoid K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
        S K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
        (@SMulZeroClass.toSMul S V
          (@AddZero.toZero V
            (@AddZeroClass.toAddZero V
              (@AddMonoid.toAddZeroClass V (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3)))))
          (@DistribSMul.toSMulZeroClass S V
            (@AddMonoid.toAddZeroClass V (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3)))
            (@DistribMulAction.toDistribSMul S V
              (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3))
              (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_3) inst_5))))
        inst_4
        (@SMulZeroClass.toSMul S K
          (@AddZero.toZero K
            (@AddZeroClass.toAddZero K
              (@AddMonoid.toAddZeroClass K
                (@AddCommMonoid.toAddMonoid K
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))))
          (@DistribSMul.toSMulZeroClass S K
            (@AddMonoid.toAddZeroClass K
              (@AddCommMonoid.toAddMonoid K
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            (@DistribMulAction.toDistribSMul S K
              (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
              (@AddCommMonoid.toAddMonoid K
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@Module.toDistribMulAction S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  inst_2)))))
        (@Semiring.toModule K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))) := by
  intros; infer_instance

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.hdual.{u_1, u_2, u_3} :
    {S : Type u_1} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : CommRing S] →
            [inst_1 : Field K] →
              [inst_2 :
                  @StarRing K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
                [inst_3 :
                    @Algebra S K (@CommRing.toCommSemiring S inst)
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                  [inst_4 : AddCommGroup V] →
                    [inst_5 :
                        @_root_.Module K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                          (@AddCommGroup.toAddCommMonoid V inst_4)] →
                      [inst_6 :
                          @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                            (@AddCommGroup.toAddCommMonoid V inst_4)] →
                        [@IsScalarTower S K V
                              (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                inst_3)
                              (@SMulZeroClass.toSMul K V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass K V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul K V
                                    (@Semiring.toMonoid K
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction K V
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
                              (@SMulZeroClass.toSMul S V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass S V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul S V
                                    (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction S V
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))] →
                          @LinearMap K K
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
                              (@LinearMap K K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                V K (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                              (@AddCommGroup.toAddCommMonoid V inst_4)
                              (@LinearMap.addCommMonoid K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                              inst_5
                              (@LinearMap.module K K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@Algebra.to_smulCommClass K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))
                                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)))
                                  (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))))) →
                            @Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 →
                              @Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 :=
    fun {S : Type u_1} {K : Type u_2} {V : Type u_3} [inst : CommRing S] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra S K (@CommRing.toCommSemiring S inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        [inst_4 : AddCommGroup V]
        [inst_5 :
          @_root_.Module K V
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_6 :
          @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_7 :
          @IsScalarTower S K V
            (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
            (@SMulZeroClass.toSMul K V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass K V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul K V
                  (@Semiring.toMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction K V
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
            (@SMulZeroClass.toSMul S V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass S V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul S V
                  (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))]
        (B :
          @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              V K (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
            (@AddCommGroup.toAddCommMonoid V inst_4)
            (@LinearMap.addCommMonoid K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            inst_5
            (@LinearMap.module K K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux2 K inst_1)))
        (L :
          @Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
            (@AddCommGroup.toAddCommMonoid V inst_4) inst_6) ↦
      ⨅ (y : V),
        ⨅ (_ :
          @Membership.mem V
            (@Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
              (@AddCommGroup.toAddCommMonoid V inst_4) inst_6)
            (@SetLike.instMembership
              (@Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6)
              V
              (@Submodule.setLike S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))
            L y),
          @Submodule.comap S S V K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)) (@AddCommGroup.toAddCommMonoid V inst_4)
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
            inst_6
            (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
            (@RingHom.id S (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))))
            (@LinearMap.restrictScalars S K V K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_6
              (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux3 S K V inst inst_1 inst_3 inst_4 inst_5 inst_6 inst_7)
              (@DFunLike.coe
                (@LinearMap K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
                  (@LinearMap K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    V K (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                  (@AddCommGroup.toAddCommMonoid V inst_4)
                  (@LinearMap.addCommMonoid K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                  inst_5
                  (@LinearMap.module K K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@UpperTheory.Reformulated.B.SelectionLemmas.aux2 K inst_1)))
                V
                (fun (x : V) ↦
                  @LinearMap K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    V K (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                (@LinearMap.instFunLike K K V
                  (@LinearMap K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    V K (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@AddCommGroup.toAddCommMonoid V inst_4)
                  (@LinearMap.addCommMonoid K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                  inst_5
                  (@LinearMap.module K K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@UpperTheory.Reformulated.B.SelectionLemmas.aux2 K inst_1))
                  (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2))
                B y))
            (@OfNat.ofNat
              (@Submodule S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3))
              (nat_lit 1)
              (@One.toOfNat1
                (@Submodule S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                  (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    inst_3))
                (@Submodule.one S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)) K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    inst_3))))

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.dual.{u_1, u_2, u_3} :
    {R : Type u_1} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : CommRing R] →
            [inst_1 : Field K] →
              [inst_2 :
                  @StarRing K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
                [inst_3 :
                    @Algebra R K (@CommRing.toCommSemiring R inst)
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                  [inst_4 : AddCommGroup V] →
                    [inst_5 :
                        @_root_.Module K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                          (@AddCommGroup.toAddCommMonoid V inst_4)] →
                      [inst_6 :
                          @_root_.Module R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid V inst_4)] →
                        [@IsScalarTower R K V
                              (@Algebra.toSMul R K (@CommRing.toCommSemiring R inst)
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                inst_3)
                              (@SMulZeroClass.toSMul K V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass K V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul K V
                                    (@Semiring.toMonoid K
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction K V
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
                              (@SMulZeroClass.toSMul R V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass R V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul R V
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction R V
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))] →
                          @LinearMap K K
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
                              (@LinearMap K K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                V K (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                              (@AddCommGroup.toAddCommMonoid V inst_4)
                              (@LinearMap.addCommMonoid K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                              inst_5
                              (@LinearMap.module K K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@Algebra.to_smulCommClass K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))
                                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)))
                                  (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))))) →
                            @Submodule R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 →
                              @Submodule R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 :=
    fun {R : Type u_1} {K : Type u_2} {V : Type u_3} [inst : CommRing R] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra R K (@CommRing.toCommSemiring R inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        [inst_4 : AddCommGroup V]
        [inst_5 :
          @_root_.Module K V
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_6 :
          @_root_.Module R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_7 :
          @IsScalarTower R K V
            (@Algebra.toSMul R K (@CommRing.toCommSemiring R inst)
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
            (@SMulZeroClass.toSMul K V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass K V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul K V
                  (@Semiring.toMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction K V
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
            (@SMulZeroClass.toSMul R V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass R V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul R V
                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))]
        (h :
          @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              V K (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
            (@AddCommGroup.toAddCommMonoid V inst_4)
            (@LinearMap.addCommMonoid K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            inst_5
            (@LinearMap.module K K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux1 K inst_1)))
        (L :
          @Submodule R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid V inst_4) inst_6) ↦
      @UpperTheory.Reformulated.B.SelectionLemmas.hdual R K V inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 h L

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux6 :
    ∀ {K : Type} [inst : Field K],
      @RingHomInvPair K K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
        (@RingHom.id K
          (@Semiring.toNonAssocSemiring K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
        (@RingHom.id K
          (@Semiring.toNonAssocSemiring K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))) := by
  intros; infer_instance

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux7 :
    ∀ {K : Type} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))) := by
  intros; infer_instance

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux8 :
    ∀ {K : Type} [inst : Field K] {n : Nat},
      @SMulCommClass K K
        (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (Fin n → K) K
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
        (@LinearMap.instSMul K K K (Fin n → K) K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@DistribMulAction.toDistribSMul K K
            (@Semiring.toMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@AddCommMonoid.toAddMonoid K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Module.toDistribMulAction K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
        (@LinearMap.instSMul K K K (Fin n → K) K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@DistribMulAction.toDistribSMul K K
            (@Semiring.toMonoid K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@AddCommMonoid.toAddMonoid K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Module.toDistribMulAction K K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)) := by
  intros; infer_instance

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.hform :
    {K : Type} →
      [inst : Field K] →
        [inst_1 :
            @StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {n : Nat} →
            Matrix (Fin n) (Fin n) K →
              @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
                (@LinearMap K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (Fin n → K) K
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Pi.Function.module (Fin n) K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@LinearMap.addCommMonoid K K (Fin n → K) K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Pi.Function.module (Fin n) K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@LinearMap.module K K K (Fin n → K) K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Pi.Function.module (Fin n) K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.to_smulCommClass K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
                    (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))) :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {n : Nat} (H : Matrix (Fin n) (Fin n) K) ↦
      @DFunLike.coe
        (@LinearEquiv K K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (Matrix (Fin n) (Fin n) K)
          (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
          (@Matrix.addCommMonoid (Fin n) (Fin n) K
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@LinearMap.addCommMonoid K K (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1))
          (@Matrix.module (Fin n) (Fin n) K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@LinearMap.module K K K (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
            (@UpperTheory.Reformulated.B.SelectionLemmas.aux8 K inst n)))
        (Matrix (Fin n) (Fin n) K)
        (fun (x : Matrix (Fin n) (Fin n) K) ↦
          @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
        (@EquivLike.toFunLike
          (@LinearEquiv K K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (Matrix (Fin n) (Fin n) K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
            (@Matrix.addCommMonoid (Fin n) (Fin n) K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.addCommMonoid K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1))
            (@Matrix.module (Fin n) (Fin n) K K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux8 K inst n)))
          (Matrix (Fin n) (Fin n) K)
          (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
          (@DFinsupp.instEquivLikeLinearEquiv K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (Matrix (Fin n) (Fin n) K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
            (@Matrix.addCommMonoid (Fin n) (Fin n) K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.addCommMonoid K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1))
            (@Matrix.module (Fin n) (Fin n) K K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux8 K inst n))))
        (@Matrix.toLinearMapₛₗ₂' K K K K K K (Fin n) (Fin n) (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)
          (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (Fin.fintype n) (Fin.fintype n) (instDecidableEqFin n) (instDecidableEqFin n))
        H

theorem UpperTheory.Reformulated.B.SelectionLemmas.laurent_T_neg_one_mul_T_one.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
      {x y : W},
      @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
            ∃ (s : R),
              And
                (@Membership.mem R
                  (@Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@SetLike.instMembership
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    R
                    (@Submonoid.instSetLike R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                  S s)
                (@Membership.mem W
                  (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    W
                    (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                  L
                  (@HSMul.hSMul R W W
                    (@instHSMul R W
                      (@SMulZeroClass.toSMul R W
                        (@AddZero.toZero W
                          (@AddZeroClass.toAddZero W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          x →
        @Membership.mem W (Set W) (@Set.instMembership W)
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                    S s)
                  (@Membership.mem W
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    (@SetLike.instMembership
                      (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                      W
                      (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                    L
                    (@HSMul.hSMul R W W
                      (@instHSMul R W
                        (@SMulZeroClass.toSMul R W
                          (@AddZero.toZero W
                            (@AddZeroClass.toAddZero W
                              (@AddMonoid.toAddZeroClass W
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            y →
          @Membership.mem W (Set W) (@Set.instMembership W)
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                    S s)
                  (@Membership.mem W
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    (@SetLike.instMembership
                      (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                      W
                      (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                    L
                    (@HSMul.hSMul R W W
                      (@instHSMul R W
                        (@SMulZeroClass.toSMul R W
                          (@AddZero.toZero W
                            (@AddZeroClass.toAddZero W
                              (@AddMonoid.toAddZeroClass W
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            (@HAdd.hAdd W W W
              (@instHAdd W
                (@AddZero.toAdd W
                  (@AddZeroClass.toAddZero W
                    (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))))))
              x y) := by
  intro R _ W _ _ S L x y hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact L.smul_mem _ hx
  · rw [mul_smul]; exact L.smul_mem _ hy

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux11.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2),
      ∃ (s : R),
        And
          (@Membership.mem R
            (@Submonoid R
              (@MulZeroOneClass.toMulOneClass R
                (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
            (@SetLike.instMembership
              (@Submonoid R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              R
              (@Submonoid.instSetLike R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
            S s)
          (@Membership.mem W
            (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
            (@SetLike.instMembership
              (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
              W
              (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
            L
            (@HSMul.hSMul R W W
              (@instHSMul R W
                (@SMulZeroClass.toSMul R W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                  (@DistribSMul.toSMulZeroClass R W
                    (@AddMonoid.toAddZeroClass W
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                    (@DistribMulAction.toDistribSMul R W
                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                      (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
              s
              (@OfNat.ofNat W (nat_lit 0)
                (@Zero.toOfNat0 W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))))))))) := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.SelectionLemmas.aux12.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
      (r : R) {x : W},
      @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
            ∃ (s : R),
              And
                (@Membership.mem R
                  (@Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@SetLike.instMembership
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    R
                    (@Submonoid.instSetLike R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                  S s)
                (@Membership.mem W
                  (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    W
                    (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                  L
                  (@HSMul.hSMul R W W
                    (@instHSMul R W
                      (@SMulZeroClass.toSMul R W
                        (@AddZero.toZero W
                          (@AddZeroClass.toAddZero W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          x →
        @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
            ∃ (s : R),
              And
                (@Membership.mem R
                  (@Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@SetLike.instMembership
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    R
                    (@Submonoid.instSetLike R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                  S s)
                (@Membership.mem W
                  (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    W
                    (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                  L
                  (@HSMul.hSMul R W W
                    (@instHSMul R W
                      (@SMulZeroClass.toSMul R W
                        (@AddZero.toZero W
                          (@AddZeroClass.toAddZero W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          (@HSMul.hSMul R W W
            (@instHSMul R W
              (@SMulZeroClass.toSMul R W
                (@AddZero.toZero W
                  (@AddZeroClass.toAddZero W
                    (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))))
                (@DistribSMul.toSMulZeroClass R W
                  (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))
                  (@DistribMulAction.toDistribSMul R W
                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))
                    (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
            r x) := by
  intro R _ W _ _ S L r x hx
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem _ hx

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 :
                @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@AddCommGroup.toAddCommMonoid W inst_1)] →
              @Submonoid R
                  (@MulZeroOneClass.toMulOneClass R
                    (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) →
                @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2 →
                  @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2 :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W]
        [inst_2 :
          @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_1)]
        (S :
          @Submonoid R
            (@MulZeroOneClass.toMulOneClass R
              (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
        (L :
          @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_1) inst_2) ↦
      @Submodule.mk R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2
        (@AddSubmonoid.mk W
          (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))
          (@AddSubsemigroup.mk W
            (@AddZero.toAdd W
              (@AddZeroClass.toAddZero W
                (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))))
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                    S s)
                  (@Membership.mem W
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    (@SetLike.instMembership
                      (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                      W
                      (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                    L
                    (@HSMul.hSMul R W W
                      (@instHSMul R W
                        (@SMulZeroClass.toSMul R W
                          (@AddZero.toZero W
                            (@AddZeroClass.toAddZero W
                              (@AddMonoid.toAddZeroClass W
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            (@UpperTheory.Reformulated.B.SelectionLemmas.laurent_T_neg_one_mul_T_one R inst W inst_1 inst_2 S L))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux11 R inst W inst_1 inst_2 S L))
        (@UpperTheory.Reformulated.B.SelectionLemmas.aux12 R inst W inst_1 inst_2 S L)

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.hcompl.{u_1, u_2} :
    {R : Type u_1} →
      {K : Type u_2} →
        [inst : CommRing R] →
          [inst_1 : Field K] →
            [@StarRing K
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                        (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
              [@Algebra R K (@CommRing.toCommSemiring R inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) →
                  @Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) :=
    fun {R : Type u_1} {K : Type u_2} [inst : CommRing R] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra R K (@CommRing.toCommSemiring R inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        (p : @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
      @Submonoid.closure R
        (@MulZeroOneClass.toMulOneClass R
          (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@Set.ofPred R fun (s : R) ↦
          And (s ∉ p)
            (∀ (t : R),
              @Eq K
                  (@DFunLike.coe
                    (@RingHom R K
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    R (fun (x : R) ↦ K)
                    (@RingHom.instFunLike R K
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    (@Algebra.algebraMap R K (@CommRing.toCommSemiring R inst)
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                      inst_3)
                    t)
                  (@Star.star K
                    (@InvolutiveStar.toStar K
                      (@StarAddMonoid.toInvolutiveStar K
                        (@AddCommMonoid.toAddMonoid K
                          (@NonUnitalNonAssocSemiring.toAddCommMonoid K
                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))))
                        (@StarRing.toStarAddMonoid K
                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                                (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))
                          inst_2)))
                    (@DFunLike.coe
                      (@RingHom R K
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Semiring.toNonAssocSemiring K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                      R (fun (x : R) ↦ K)
                      (@RingHom.instFunLike R K
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Semiring.toNonAssocSemiring K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                      (@Algebra.algebraMap R K (@CommRing.toCommSemiring R inst)
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                        inst_3)
                      s)) →
                t ∉ p))

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.loc.{u_1, u_2, u_4} :
    {R : Type u_1} →
      {K : Type u_2} →
        [inst : CommRing R] →
          [inst_1 : Field K] →
            [@StarRing K
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                        (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
              [@Algebra R K (@CommRing.toCommSemiring R inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                {W : Type u_4} →
                  [inst_4 : AddCommGroup W] →
                    [inst_5 :
                        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid W inst_4)] →
                      @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) →
                        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid W inst_4) inst_5 →
                          @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid W inst_4) inst_5 :=
    fun {R : Type u_1} {K : Type u_2} [inst : CommRing R] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra R K (@CommRing.toCommSemiring R inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        {W : Type u_4} [inst_4 : AddCommGroup W]
        [inst_5 :
          @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_4)]
        (p : @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
        (L :
          @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_4) inst_5) ↦
      @UpperTheory.Reformulated.B.SelectionLemmas.locS R inst W inst_4 inst_5 (@UpperTheory.Reformulated.B.SelectionLemmas.hcompl R K inst inst_1 inst_2 inst_3 p) L

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.IsLocBasis :
    {K : Type} →
      [inst : Field K] →
        [@StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {D : Nat} →
            @Submodule (@NumberField.RingOfIntegers K inst) (Fin D → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst))) →
              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst) →
                (Fin D → Fin D → K) → Prop :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {D : Nat}
        (L :
          @Submodule (@NumberField.RingOfIntegers K inst) (Fin D → K)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Pi.addCommMonoid (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
        (w :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
            (@NumberField.instCommRingRingOfIntegers K inst))
        (e : Fin D → Fin D → K) ↦
      And
        (@LinearIndependent (Fin D) K (Fin D → K) e
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin D) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
        (@Eq
          (@Submodule (@NumberField.RingOfIntegers K inst) (Fin D → K)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid (Fin D → K)
              (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.loc (@NumberField.RingOfIntegers K inst) K (@NumberField.instCommRingRingOfIntegers K inst) inst
            inst_1 (@NumberField.RingOfIntegers.instAlgebra_1 K inst) (Fin D → K)
            (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
              @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
            (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst) w)
            (@Submodule.span (@NumberField.RingOfIntegers K inst) (Fin D → K)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@AddCommGroup.toAddCommMonoid (Fin D → K)
                (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                  @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
              (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Semiring.toAddCommMonoid K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
              (@Set.range (Fin D → K) (Fin D) e)))
          (@UpperTheory.Reformulated.B.SelectionLemmas.loc (@NumberField.RingOfIntegers K inst) K (@NumberField.instCommRingRingOfIntegers K inst) inst
            inst_1 (@NumberField.RingOfIntegers.instAlgebra_1 K inst) (Fin D → K)
            (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
              @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
            (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst) w)
            L))

theorem UpperTheory.Reformulated.B.SelectionLemmas.complex_normed_instance_compat :
    ∀ {K : Type} [inst : Field K],
      @RingHomSurjective (@NumberField.RingOfIntegers K inst) (@NumberField.RingOfIntegers K inst)
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@RingHom.id (@NumberField.RingOfIntegers K inst)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers K inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))))) := by
  intros; infer_instance

theorem UpperTheory.Reformulated.B.SelectionLemmas.padic_embedding_algebra_compat :
    ∀ {K : Type} [inst : Field K] {d d' : Nat},
      @LinearMap.CompatibleSMul (Fin d → K) (Fin d' → K)
        (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
          @Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
          @Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@NumberField.RingOfIntegers K inst) K
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
        (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) (Fin d → K)
          (@AddZero.toZero (Fin d → K)
            (@AddZeroClass.toAddZero (Fin d → K)
              (@AddMonoid.toAddZeroClass (Fin d → K)
                (@AddCommMonoid.toAddMonoid (Fin d → K)
                  (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                    @Semiring.toAddCommMonoid K
                      (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))))
          (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) (Fin d → K)
            (@AddMonoid.toAddZeroClass (Fin d → K)
              (@AddCommMonoid.toAddMonoid (Fin d → K)
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))
            (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) (Fin d → K)
              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))))
              (@AddCommMonoid.toAddMonoid (Fin d → K)
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
              (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) (Fin d → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))))
        (@Pi.Function.module (Fin d) K K
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
        (@Function.hasSMul (Fin d') (@NumberField.RingOfIntegers K inst) K
          (@SemigroupAction.toSMul (@NumberField.RingOfIntegers K inst) K
            (@Monoid.toSemigroup (@NumberField.RingOfIntegers K inst)
              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))))
            (@MulAction.toSemigroupAction (@NumberField.RingOfIntegers K inst) K
              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))))
              (@DistribMulAction.toMulAction (@NumberField.RingOfIntegers K inst) K
                (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))
                (@AddCommMonoid.toAddMonoid K
                  (@Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
                (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))))
        (@Pi.Function.module (Fin d') K K
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))) := by
  intros; infer_instance

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.matLat :
    {K : Type} →
      [inst : Field K] →
        {d d' : Nat} →
          Matrix (Fin d') (Fin d) K →
            @Submodule (@NumberField.RingOfIntegers K inst) (Fin d → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst))) →
              @Submodule (@NumberField.RingOfIntegers K inst) (Fin d' → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin d') (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst))) :=
    fun {K : Type} [inst : Field K] {d d' : Nat} (φ : Matrix (Fin d') (Fin d) K)
        (L :
          @Submodule (@NumberField.RingOfIntegers K inst) (Fin d → K)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))) ↦
      @Submodule.map (@NumberField.RingOfIntegers K inst) (@NumberField.RingOfIntegers K inst) (Fin d → K) (Fin d' → K)
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
          @Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
          @Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
        (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
        (@Pi.Function.module (Fin d') (@NumberField.RingOfIntegers K inst) K
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
        (@RingHom.id (@NumberField.RingOfIntegers K inst)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers K inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))))
        (@UpperTheory.Reformulated.B.SelectionLemmas.complex_normed_instance_compat K inst)
        (@LinearMap.restrictScalars (@NumberField.RingOfIntegers K inst) K (Fin d → K) (Fin d' → K)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
            @Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
            @Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
          (@Pi.Function.module (Fin d') (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
          (@Pi.Function.module (Fin d) K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@Pi.Function.module (Fin d') K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.padic_embedding_algebra_compat K inst d d')
          (@Matrix.mulVecLin K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) (Fin d') (Fin d) (Fin.fintype d)
            φ))
        L

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.vw :
    {K : Type} →
      [inst : Field K] →
        [@NumberField K inst] →
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst) →
            K → Int :=
    fun {K : Type} [inst : Field K] [inst_1 : @NumberField K inst]
        (w :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
            (@NumberField.instCommRingRingOfIntegers K inst))
        (a : K) ↦
      @FractionalIdeal.count (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst) K inst
        (@NumberField.RingOfIntegers.instAlgebra_1 K inst) (@NumberField.RingOfIntegers.instIsFractionRing K inst inst_1)
        (@NumberField.RingOfIntegers.instIsDedekindDomain K inst inst_1) w
        (@FractionalIdeal.spanSingleton (@NumberField.RingOfIntegers K inst)
          (@NumberField.instCommRingRingOfIntegers K inst)
          (@nonZeroDivisors (@NumberField.RingOfIntegers K inst)
            (@Semiring.toMonoidWithZero (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))))
          K (@Field.toCommRing K inst) (@NumberField.RingOfIntegers.instAlgebra_1 K inst)
          (@NumberField.RingOfIntegers.instIsFractionRing K inst inst_1) a)

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.gramR :
    {K : Type} →
      [inst : Field K] →
        [@StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {D m : Nat} → Matrix (Fin D) (Fin D) K → (Fin m → Fin D → K) → K :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {D m : Nat} (Γ : Matrix (Fin D) (Fin D) K) (e : Fin m → Fin D → K) ↦
      @Matrix.det (Fin m) (instDecidableEqFin m) (Fin.fintype m) K (@Field.toCommRing K inst)
        (@DFunLike.coe (Equiv (Fin m → Fin m → K) (Matrix (Fin m) (Fin m) K)) (Fin m → Fin m → K)
          (fun (x : Fin m → Fin m → K) ↦ Matrix (Fin m) (Fin m) K)
          (@EquivLike.toFunLike (Equiv (Fin m → Fin m → K) (Matrix (Fin m) (Fin m) K)) (Fin m → Fin m → K)
            (Matrix (Fin m) (Fin m) K) (@Equiv.instEquivLike (Fin m → Fin m → K) (Matrix (Fin m) (Fin m) K)))
          (@Matrix.of (Fin m) (Fin m) K) fun (a b : Fin m) ↦
          @dotProduct (Fin D) K (Fin.fintype D)
            (@Distrib.toMul K
              (@instDistribOfSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Star.star (Fin D → K)
              (@Pi.instStarForall (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                @InvolutiveStar.toStar K
                  (@StarAddMonoid.toInvolutiveStar K
                    (@AddCommMonoid.toAddMonoid K
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid K
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                              (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))))
                    (@StarRing.toStarAddMonoid K
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                            (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))
                      inst_1)))
              (e a))
            (@Matrix.mulVec (Fin D) (Fin D) K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))
              (Fin.fintype D) Γ (e b)))

noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.quotGram :
    {K : Type} →
      [inst : Field K] →
        [@StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {n D : Nat} → Matrix (Fin D) (Fin n) K → Matrix (Fin n) (Fin n) K → Matrix (Fin D) (Fin D) K :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {n D : Nat} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) ↦
      @Inv.inv (Matrix (Fin D) (Fin D) K)
        (@Matrix.inv (Fin D) K (Fin.fintype D) (instDecidableEqFin D) (@Field.toCommRing K inst))
        (@HMul.hMul (Matrix (Fin D) (Fin n) K) (Matrix (Fin n) (Fin D) K) (Matrix (Fin D) (Fin D) K)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin D) (Fin n) (Fin D) K (Fin.fintype n)
            (@Distrib.toMul K
              (@instDistribOfSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@HMul.hMul (Matrix (Fin D) (Fin n) K) (Matrix (Fin n) (Fin n) K) (Matrix (Fin D) (Fin n) K)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin D) (Fin n) (Fin n) K (Fin.fintype n)
              (@Distrib.toMul K
                (@instDistribOfSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            P
            (@Inv.inv (Matrix (Fin n) (Fin n) K)
              (@Matrix.inv (Fin n) K (Fin.fintype n) (instDecidableEqFin n) (@Field.toCommRing K inst)) H))
          (@Matrix.conjTranspose (Fin D) (Fin n) K
            (@InvolutiveStar.toStar K
              (@StarAddMonoid.toInvolutiveStar K
                (@AddCommMonoid.toAddMonoid K
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))))
                (@StarRing.toStarAddMonoid K
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                        (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))
                  inst_1)))
            P))

section Helpers
open NumberField IsDedekindDomain Matrix
namespace UpperTheory.Reformulated.B.SelectionLemmas

private theorem star_int {K : Type} [Field K] [StarRing K] (a : 𝓞 K) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = star (algebraMap (𝓞 K) K a) := by
  have h : IsIntegral ℤ ((starRingEnd K).toIntAlgHom (algebraMap (𝓞 K) K a)) :=
    (RingOfIntegers.isIntegral_coe a).map _
  exact ⟨⟨_, h⟩, rfl⟩

private theorem hcompl_spec {K : Type} [Field K] [StarRing K] (p : Ideal (𝓞 K)) (hp : p.IsPrime)
    (s : 𝓞 K) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p ∧ ∃ t : 𝓞 K, t ∉ p ∧ algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) := by
  unfold hcompl at hs
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht⟩ := star_int x
    exact ⟨hx.1, t, hx.2 t ht, ht⟩
  | one => exact ⟨(Ideal.ne_top_iff_one p).1 hp.ne_top, 1, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx, t, ht, ht'⟩ := hx
    obtain ⟨hy, u, hu, hu'⟩ := hy
    refine ⟨fun h => (hp.mem_or_mem h).elim hx hy, t * u, fun h => (hp.mem_or_mem h).elim ht hu, ?_⟩
    rw [map_mul, map_mul, ht', hu', star_mul']

private theorem exists_uniform {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
    (S : Submonoid R) (N L : Submodule R W) (hN : N.FG) (h : N ≤ locS S L) :
    ∃ s ∈ S, ∀ y ∈ N, s • y ∈ L := by
  induction N, hN using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨s, hs, hx⟩ := h (Submodule.mem_span_singleton_self x)
    refine ⟨s, hs, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [smul_comm]
    exact L.smul_mem _ hx
  | sup N₁ N₂ _ _ h₁ h₂ =>
    obtain ⟨s, hs, h₁⟩ := h₁ (le_sup_left.trans h)
    obtain ⟨t, ht, h₂⟩ := h₂ (le_sup_right.trans h)
    refine ⟨s * t, S.mul_mem hs ht, fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ (h₁ a ha)
    · rw [mul_smul]; exact L.smul_mem _ (h₂ b hb)

private theorem vw_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.2 ha
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.2 hb

private theorem vw_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (a : K) (m : ℕ) : vw w (a ^ m) = m * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

private theorem vw_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    vw w (0 : K) = 0 := by
  unfold vw
  rw [FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]

private theorem vw_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    vw w (1 : K) = 0 := by
  unfold vw
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

private theorem vw_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) : 0 ≤ vw w (algebraMap (𝓞 K) K a) := by
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

private theorem vw_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ∉ w.asIdeal) : vw w (algebraMap (𝓞 K) K a) = 0 := by
  classical
  have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    intro h
    rw [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at h
    exact ha (h ▸ w.asIdeal.zero_mem)
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w h0]
  by_contra hne
  have hne' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
    exact_mod_cast hne
  have := (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 hne'
  exact ha (Ideal.dvd_span_singleton.1 this)

private theorem det_int {K : Type} [Field K] {D : ℕ} (A : Matrix (Fin D) (Fin D) K)
    (h : ∀ i j, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = A i j) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = A.det := by
  choose B hB using h
  refine ⟨(Matrix.of B).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hB i j

private theorem core {K : Type} [Field K] [StarRing K] {n D : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : IsUnit H.det) (B : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (c : K)
    (hc : ∀ x ∈ dual (hform H) M, c • x ∈ M) (s t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s))
    (hs : ∀ y ∈ M, ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K s * (B *ᵥ y) i)
    (i j : Fin D) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a =
      ((algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K t * c) • (B * H⁻¹ * Bᴴ)) i j := by
  have hx : algebraMap (𝓞 K) K t • (H⁻¹ *ᵥ star (B j)) ∈ dual (hform H) M := by
    unfold dual hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    intro y hy
    obtain ⟨a, ha⟩ := hs y hy j
    obtain ⟨b, hb⟩ := star_int a
    refine ⟨b, ?_⟩
    rw [hb, ha, LinearMap.restrictScalars_apply, map_smul]
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    have h1 : H *ᵥ (H⁻¹ *ᵥ star (B j)) = star (B j) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
    have h2 : ∀ v : Fin n → K, ∑ a, ∑ b, (starRingEnd K) (y a) • (RingHom.id K) (v b) • H a b
        = star y ⬝ᵥ (H *ᵥ v) := by
      intro v
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, smul_eq_mul, RingHom.id_apply,
        starRingEnd_apply, Pi.star_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [h2, h1, star_mul', ← ht, smul_eq_mul]
    congr 1
    simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]
  obtain ⟨a, ha⟩ := hs _ (hc _ hx) i
  refine ⟨a, ?_⟩
  rw [ha, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.smul_apply,
    Matrix.mul_apply (M := B * H⁻¹)]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Pi.star_apply]
  ring

end UpperTheory.Reformulated.B.SelectionLemmas
end Helpers

theorem UpperTheory.Reformulated.B.SelectionLemmas.main :
    ∀ {K : Type} [inst : Field K] [inst_1 : @NumberField K inst]
      [inst_2 :
        @StarRing K
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
      {n D : Nat} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
      (M :
        @Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))),
      @Submodule.FG (@NumberField.RingOfIntegers K inst) (Fin n → K)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
          M →
        ∀ (l g : Nat),
          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) l →
            (∀ (x : Fin n → K),
                @Membership.mem (Fin n → K)
                    (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))
                      (@AddCommGroup.toAddCommMonoid (Fin n → K)
                        (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                          @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                      (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                    (@SetLike.instMembership
                      (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@AddCommGroup.toAddCommMonoid (Fin n → K)
                          (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                            @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                      (Fin n → K)
                      (@Submodule.setLike (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@AddCommGroup.toAddCommMonoid (Fin n → K)
                          (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                            @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))
                    (@UpperTheory.Reformulated.B.SelectionLemmas.dual (@NumberField.RingOfIntegers K inst) K (Fin n → K)
                      (@NumberField.instCommRingRingOfIntegers K inst) inst inst_2
                      (@NumberField.RingOfIntegers.instAlgebra_1 K inst)
                      (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                        @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                      (@Pi.Function.module (Fin n) K K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Semiring.toModule K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                      (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
                      (@Pi.isScalarTower (Fin n) (@NumberField.RingOfIntegers K inst) K (fun (a : Fin n) ↦ K)
                        (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
                        (fun (i : Fin n) ↦
                          @SemigroupAction.toSMul K ((fun (a : Fin n) ↦ K) i)
                            (@Monoid.toSemigroup K
                              (@Semiring.toMonoid K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                            (@MulAction.toSemigroupAction K ((fun (a : Fin n) ↦ K) i)
                              (@Semiring.toMonoid K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                              ((fun (i : Fin n) ↦
                                  @DistribMulAction.toMulAction K ((fun (a : Fin n) ↦ K) i)
                                    (@Semiring.toMonoid K
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                    ((fun (i : Fin n) ↦
                                        @AddCommMonoid.toAddMonoid ((fun (a : Fin n) ↦ K) i)
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i))
                                      i)
                                    ((fun (i : Fin n) ↦
                                        @Module.toDistribMulAction K ((fun (a : Fin n) ↦ K) i)
                                          (@DivisionSemiring.toSemiring K
                                            (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i)
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toModule K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i))
                                      i))
                                i)))
                        (fun (i : Fin n) ↦
                          @SemigroupAction.toSMul (@NumberField.RingOfIntegers K inst) ((fun (a : Fin n) ↦ K) i)
                            (@Monoid.toSemigroup (@NumberField.RingOfIntegers K inst)
                              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                    (@NumberField.instCommRingRingOfIntegers K inst)))))
                            (@MulAction.toSemigroupAction (@NumberField.RingOfIntegers K inst) ((fun (a : Fin n) ↦ K) i)
                              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                    (@NumberField.instCommRingRingOfIntegers K inst))))
                              ((fun (i : Fin n) ↦
                                  @DistribMulAction.toMulAction (@NumberField.RingOfIntegers K inst)
                                    ((fun (a : Fin n) ↦ K) i)
                                    (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                          (@NumberField.instCommRingRingOfIntegers K inst))))
                                    ((fun (i : Fin n) ↦
                                        @AddCommMonoid.toAddMonoid ((fun (a : Fin n) ↦ K) i)
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i))
                                      i)
                                    ((fun (i : Fin n) ↦
                                        @Module.toDistribMulAction (@NumberField.RingOfIntegers K inst)
                                          ((fun (a : Fin n) ↦ K) i)
                                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                              (@NumberField.instCommRingRingOfIntegers K inst)))
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i)
                                          ((fun (i : Fin n) ↦
                                              @Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                                                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                                  (@NumberField.instCommRingRingOfIntegers K inst))
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                                                (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
                                            i))
                                      i))
                                i)))
                        fun (i : Fin n) ↦
                        @IsScalarTower.right (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
                      (@UpperTheory.Reformulated.B.SelectionLemmas.hform K inst inst_2 n H) M)
                    x →
                  @Membership.mem (Fin n → K)
                    (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                      (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                    (@SetLike.instMembership
                      (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                          @Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                      (Fin n → K)
                      (@Submodule.setLike (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                          @Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))
                    M
                    (@HSMul.hSMul (@NumberField.RingOfIntegers K inst) (Fin n → K) (Fin n → K)
                      (@instHSMul (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@Function.hasSMul (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                      (@HPow.hPow (@NumberField.RingOfIntegers K inst) Nat (@NumberField.RingOfIntegers K inst)
                        (@instHPow (@NumberField.RingOfIntegers K inst) Nat
                          (@NPow.toPow (@NumberField.RingOfIntegers K inst)
                            (@Monoid.toNPow (@NumberField.RingOfIntegers K inst)
                              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                    (@NumberField.instCommRingRingOfIntegers K inst)))))))
                        (@Nat.cast (@NumberField.RingOfIntegers K inst)
                          (@AddMonoidWithOne.toNatCast (@NumberField.RingOfIntegers K inst)
                            (@AddGroupWithOne.toAddMonoidWithOne (@NumberField.RingOfIntegers K inst)
                              (@Ring.toAddGroupWithOne (@NumberField.RingOfIntegers K inst)
                                (@CommRing.toRing (@NumberField.RingOfIntegers K inst)
                                  (@NumberField.instCommRingRingOfIntegers K inst)))))
                          l)
                        g)
                      x)) →
              ∀
                (w :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                (e : Fin D → Fin D → K),
                @UpperTheory.Reformulated.B.SelectionLemmas.IsLocBasis K inst inst_2 D (@UpperTheory.Reformulated.B.SelectionLemmas.matLat K inst n D P M) w e →
                  @LE.le Int Int.instLEInt
                    (@UpperTheory.Reformulated.B.SelectionLemmas.vw K inst inst_1 w
                      (@UpperTheory.Reformulated.B.SelectionLemmas.gramR K inst inst_2 D D (@UpperTheory.Reformulated.B.SelectionLemmas.quotGram K inst inst_2 n D P H) e))
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@Nat.cast Int instNatCastInt g)
                        (@Nat.cast Int instNatCastInt D))
                      (@UpperTheory.Reformulated.B.SelectionLemmas.vw K inst inst_1 w
                        (@Nat.cast K
                          (@AddMonoidWithOne.toNatCast K
                            (@AddGroupWithOne.toAddMonoidWithOne K
                              (@Ring.toAddGroupWithOne K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))))
                          l))) := by
  open NumberField Matrix UpperTheory.Reformulated.B.SelectionLemmas in
  intro K _ _ _ n D H P M hM l g hl hc w e he
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hl.ne'
  have hvl : 0 ≤ vw w (l : K) := by simpa using vw_nonneg w (l : 𝓞 K)
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have : gramR (quotGram P H) e = 1 := Matrix.det_isEmpty
    rw [this, vw_one]
    simp
  by_cases hG : gramR (quotGram P H) e = 0
  · rw [hG, vw_zero]
    positivity
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  set E : Matrix (Fin D) (Fin D) K := (Matrix.of e)ᵀ with hE
  have hgram : gramR (quotGram P H) e = (Eᴴ * (P * H⁻¹ * Pᴴ)⁻¹ * E).det := by
    unfold gramR quotGram
    congr 1
    ext a b
    rw [Matrix.mul_assoc Eᴴ, Matrix.mul_apply]
    rfl
  have hG' := hG
  rw [hgram, Matrix.det_mul, Matrix.det_mul] at hG'
  have hEu : IsUnit E.det := (right_ne_zero_of_mul hG').isUnit
  have hEu' : IsUnit Eᴴ.det := (left_ne_zero_of_mul (left_ne_zero_of_mul hG')).isUnit
  have hA : IsUnit (P * H⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.det_zero] at hG'
    all_goals first | exact hG' (by simp) | infer_instance
  have hH : IsUnit H.det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.det_zero] at hA
    all_goals first | exact not_isUnit_zero hA | infer_instance
  have hle : matLat P M ≤ locS (hcompl (K := K) w.asIdeal) (Submodule.span (𝓞 K) (Set.range e)) := by
    intro x hx
    have h1 : x ∈ loc (K := K) w.asIdeal (matLat P M) :=
      ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
    rw [← he.2] at h1
    exact h1
  obtain ⟨s, hsS, hs⟩ := exists_uniform _ _ _ (hM.map _) hle
  obtain ⟨hsw, t, htw, ht⟩ := hcompl_spec _ w.isPrime s hsS
  have hs' : ∀ y ∈ M, ∀ i, ∃ a : 𝓞 K,
      algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K s * ((E⁻¹ * P) *ᵥ y) i := by
    intro y hy i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hs (P *ᵥ y) (Submodule.mem_map_of_mem hy))
    refine ⟨a i, ?_⟩
    have h1 : E *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = algebraMap (𝓞 K) K s • (P *ᵥ y) := by
      rw [algebraMap_smul, ← ha]
      ext k
      simp [hE, Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
    have h2 := congrArg (fun v => (E⁻¹ *ᵥ v) i) h1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec,
      Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  obtain ⟨a, ha⟩ := det_int _ (core H hH (E⁻¹ * P) M ((l : K) ^ g) hc s t ht hs')
  have hN : (E⁻¹ * P * H⁻¹ * (E⁻¹ * P)ᴴ) * (Eᴴ * (P * H⁻¹ * Pᴴ)⁻¹ * E) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    calc E⁻¹ * P * H⁻¹ * (Pᴴ * Eᴴ⁻¹) * (Eᴴ * (P * H⁻¹ * Pᴴ)⁻¹ * E)
        = E⁻¹ * ((P * H⁻¹ * Pᴴ) * ((Eᴴ⁻¹ * Eᴴ) * (P * H⁻¹ * Pᴴ)⁻¹)) * E := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hEu', Matrix.one_mul, Matrix.mul_nonsing_inv _ hA,
            Matrix.mul_one, Matrix.nonsing_inv_mul _ hEu]
  have hdet := congrArg Matrix.det hN
  rw [Matrix.det_mul, ← hgram, Matrix.det_one] at hdet
  rw [Matrix.det_smul, Fintype.card_fin] at ha
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := fun h =>
    hsw (((FaithfulSMul.algebraMap_eq_zero_iff _ _).1 h) ▸ w.asIdeal.zero_mem)
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := fun h =>
    htw (((FaithfulSMul.algebraMap_eq_zero_iff _ _).1 h) ▸ w.asIdeal.zero_mem)
  have hkey : algebraMap (𝓞 K) K a * gramR (quotGram P H) e
      = (algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K t * (l : K) ^ g) ^ D := by
    rw [ha, mul_assoc, hdet, mul_one]
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
    refine left_ne_zero_of_mul (b := gramR (quotGram P H) e) ?_
    rw [hkey]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hs0 ht0) (pow_ne_zero _ hl0))
  have hv := congrArg (vw w) hkey
  rw [vw_mul w ha0 hG, vw_pow, vw_mul w (mul_ne_zero hs0 ht0) (pow_ne_zero _ hl0),
    vw_mul w hs0 ht0, vw_pow, vw_eq_zero w s hsw, vw_eq_zero w t htw] at hv
  have := vw_nonneg w a
  linarith
