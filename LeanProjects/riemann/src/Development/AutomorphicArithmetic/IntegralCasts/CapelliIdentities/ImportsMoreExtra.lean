import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

theorem UpperTheory.Reformulated.B.Qh15.aux1 :
    ∀ {A : Type} [inst : CommRing A],
      @SMulCommClass A A A
        (@Algebra.toSMul A A (@CommRing.toCommSemiring A inst)
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) (@Algebra.id A (@CommRing.toCommSemiring A inst)))
        (@instSMulOfMul A
          (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))) := by
  intro A _
  infer_instance

theorem UpperTheory.Reformulated.B.Qh15.aux2 :
    ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A]
      (κ :
        @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
          (@MulOneClass.toMulOne
            (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@Units.instMulOneClass A
              (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))),
      @Eq
        (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
        (@HSMul.hSMul A
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@instHSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@NonUnitalNonAssocSemiring.toDistribSMul A
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
              (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
          (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@DFunLike.coe
              (@MonoidHom G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              G
              (fun (x : G) ↦
                @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MonoidHom.instFunLike G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              κ
              (@OfNat.ofNat G (nat_lit 1)
                (@One.toOfNat1 G
                  (@MulOne.toOne G
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)))))))))
          (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
        (@OfNat.ofNat
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (nat_lit 1)
          (@One.toOfNat1
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOne.toOne
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulOneClass.toMulOne
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulZeroOneClass.toMulOneClass
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@instMulZeroOneClassOfSemiring
                    (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@RingHom.id A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))))))) := by
  intro G A _ _ κ
  ext
  simp

theorem UpperTheory.Reformulated.B.Qh15.aux3 :
    ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A]
      (κ :
        @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
          (@MulOneClass.toMulOne
            (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@Units.instMulOneClass A
              (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
      (g h : G),
      @Eq
        (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
        (@HSMul.hSMul A
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@instHSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@NonUnitalNonAssocSemiring.toDistribSMul A
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
              (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
          (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@DFunLike.coe
              (@MonoidHom G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              G
              (fun (x : G) ↦
                @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MonoidHom.instFunLike G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              κ
              (@HMul.hMul G G G
                (@instHMul G
                  (@MulOne.toMul G
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))))
                g h)))
          (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
        (@HMul.hMul
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@instHMul
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOne.toMul
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulOneClass.toMulOne
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulZeroOneClass.toMulOneClass
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@instMulZeroOneClassOfSemiring
                    (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@RingHom.id A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))))))
          (@HSMul.hSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@instHSMul A
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@NonUnitalNonAssocSemiring.toDistribSMul A
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
                (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
            (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@DFunLike.coe
                (@MonoidHom G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                G
                (fun (x : G) ↦
                  @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MonoidHom.instFunLike G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                κ g))
            (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
          (@HSMul.hSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@instHSMul A
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@NonUnitalNonAssocSemiring.toDistribSMul A
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
                (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
            (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@DFunLike.coe
                (@MonoidHom G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                G
                (fun (x : G) ↦
                  @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MonoidHom.instFunLike G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                κ h))
            (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))) := by
  intro G A _ _ κ g h
  ext
  simp [mul_comm]

noncomputable def UpperTheory.Reformulated.B.Qh15.chRep :
    {G A : Type} →
      [inst : Group G] →
        [inst_1 : CommRing A] →
          @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
              (@MulOneClass.toMulOne
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@Units.instMulOneClass A
                  (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))) →
            @Representation A G A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))) :=
    fun {G A : Type} [inst : Group G] [inst_1 : CommRing A]
        (κ :
          @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
            (@MulOneClass.toMulOne
              (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@Units.instMulOneClass A
                (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))) ↦
      @MonoidHom.mk G
        (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
        (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
        (@MulOneClass.toMulOne
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulZeroOneClass.toMulOneClass
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@instMulZeroOneClassOfSemiring
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))))
        (@OneHom.mk G
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulOne.toOne G
            (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)))))
          (@MulOne.toOne
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOneClass.toMulOne
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulZeroOneClass.toMulOneClass
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@instMulZeroOneClassOfSemiring
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))))
          (fun (g : G) ↦
            @HSMul.hSMul A
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@instHSMul A
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@NonUnitalNonAssocSemiring.toDistribSMul A
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
                  (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
              (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@DFunLike.coe
                  (@MonoidHom G
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@MulOneClass.toMulOne
                      (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      (@Units.instMulOneClass A
                        (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                  G
                  (fun (x : G) ↦
                    @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MonoidHom.instFunLike G
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@MulOneClass.toMulOne
                      (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      (@Units.instMulOneClass A
                        (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                  κ g))
              (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
          (@UpperTheory.Reformulated.B.Qh15.aux2 G A inst inst_1 κ))
        (@UpperTheory.Reformulated.B.Qh15.aux3 G A inst inst_1 κ)

theorem UpperTheory.Reformulated.B.Qh15.act_mul :
    ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp] [inst_2 : Field K₀] [inst_3 : Field K]
      [inst_4 :
        @Algebra Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2)))]
      [inst_5 :
        @Algebra Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3)))]
      [inst_6 :
        @Algebra K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3)))]
      [inst_7 :
        @IsScalarTower Qp K₀ K
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2))) inst_4)
          (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_6)
          (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_5)]
      {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR]
      [inst_10 :
        @Algebra Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8))]
      [inst_11 :
        @Algebra K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
          (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8))]
      [inst_12 :
        @IsScalarTower Qp K₀ B
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2))) inst_4)
          (@Algebra.toSMul K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_11)
          (@Algebra.toSMul Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)]
      [inst_13 :
        @Algebra Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9))]
      [inst_14 :
        @Algebra K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9))]
      [inst_15 :
        @Algebra K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_3))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9))]
      [inst_16 :
        @IsScalarTower Qp K BdR
          (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_5)
          (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_15)
          (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_13)]
      [inst_17 :
        @IsScalarTower K₀ K BdR
          (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_6)
          (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_15)
          (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_14)]
      [inst_18 :
        @IsScalarTower Qp K₀ BdR
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2))) inst_4)
          (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_14)
          (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_13)]
      (PD :
        @Formalism.WeaklyAdmissibleFiltrations.PeriodData G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
          inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18)
      {E : Type} [inst_19 : Field E]
      [inst_20 :
        @Algebra Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))]
      (κ :
        @MonoidHom G
          (@Units E
            (@Semiring.toMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
          (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
          (@MulOneClass.toMulOne
            (@Units E
              (@Semiring.toMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
            (@Units.instMulOneClass E
              (@Semiring.toMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))))
      (g : G)
      (x y :
        @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
          (@Semiring.toAddCommMonoid E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
          (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
          (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
          (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)),
      @Eq
        (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
          (@AddCommGroup.toAddCommMonoid E
            (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
          (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
          (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
          (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
        (@HMul.hMul
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@instHMul
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@Algebra.TensorProduct.instMul Qp E B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                    (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_19)))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.to_smulCommClass Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring B
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing B
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing B (@CommRing.toNonUnitalCommRing B inst_8))))
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@Algebra.to_smulCommClass Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.right Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)))
          (@DFunLike.coe
            (@LinearMap E E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20))))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (fun
                (x :
                  @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                    (@AddCommGroup.toAddCommMonoid E
                      (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                    (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                    (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                      inst_20)
                    (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)) ↦
              @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@LinearMap.instFunLike E E
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))))
            (@Formalism.WeaklyAdmissibleFiltrations.actVB G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 PD E inst_19 inst_20 E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19)))
              (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@UpperTheory.Reformulated.B.Qh15.chRep G E inst (@Field.toCommRing E inst_19) κ) g)
            x)
          (@DFunLike.coe
            (@LinearMap E E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20))))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (fun
                (x :
                  @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                    (@AddCommGroup.toAddCommMonoid E
                      (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                    (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                    (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                      inst_20)
                    (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)) ↦
              @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@LinearMap.instFunLike E E
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))))
            (@Formalism.WeaklyAdmissibleFiltrations.actVB G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 PD E inst_19 inst_20 E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19)))
              (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@UpperTheory.Reformulated.B.Qh15.chRep G E inst (@Field.toCommRing E inst_19)
                (@Inv.inv
                  (@MonoidHom G
                    (@Units E
                      (@Semiring.toMonoid E
                        (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19)))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@MulOneClass.toMulOne
                      (@Units E
                        (@Semiring.toMonoid E
                          (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19)))))
                      (@Units.instMulOneClass E
                        (@Semiring.toMonoid E
                          (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19)))))))
                  (@MonoidHom.instInv G
                    (@Units E
                      (@Semiring.toMonoid E
                        (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19)))))
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)))
                    (@Units.instCommGroupUnits E (@CommRing.toCommMonoid E (@Field.toCommRing E inst_19))))
                  κ))
              g)
            y))
        (@DFunLike.coe
          (@LinearMap E E (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@RingHom.id E
              (@Semiring.toNonAssocSemiring E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20)))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20))))
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (fun
              (x :
                @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)) ↦
            @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@LinearMap.instFunLike E E
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20)))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20)))
            (@RingHom.id E
              (@Semiring.toNonAssocSemiring E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))))
          (@Formalism.WeaklyAdmissibleFiltrations.actVB G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
            inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 PD E inst_19 inst_20 E
            (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19)))
            (@Semiring.toModule E (@CommSemiring.toSemiring E (@CommRing.toCommSemiring E (@Field.toCommRing E inst_19))))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@UpperTheory.Reformulated.B.Qh15.chRep G E inst (@Field.toCommRing E inst_19)
              (@OfNat.ofNat
                (@MonoidHom G
                  (@Units E
                    (@Semiring.toMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units E
                      (@Semiring.toMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
                    (@Units.instMulOneClass E
                      (@Semiring.toMonoid E
                        (@DivisionSemiring.toSemiring E
                          (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))))
                (nat_lit 1)
                (@One.toOfNat1
                  (@MonoidHom G
                    (@Units E
                      (@Semiring.toMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@MulOneClass.toMulOne
                      (@Units E
                        (@Semiring.toMonoid E
                          (@DivisionSemiring.toSemiring E
                            (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
                      (@Units.instMulOneClass E
                        (@Semiring.toMonoid E
                          (@DivisionSemiring.toSemiring E
                            (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))))
                  (@instOneMonoidHom G
                    (@Units E
                      (@Semiring.toMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@Units.instMulOneClass E
                      (@Semiring.toMonoid E
                        (@DivisionSemiring.toSemiring E
                          (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))))))
            g)
          (@HMul.hMul
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@instHMul
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@Algebra.TensorProduct.instMul Qp E B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                      (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_19)))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.to_smulCommClass Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring B
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing B
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing B (@CommRing.toNonUnitalCommRing B inst_8))))
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@Algebra.to_smulCommClass Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.right Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)))
            x y)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ κ g x y
  have hch : ∀ (μ : G →* Eˣ) (a : E), UpperTheory.Reformulated.B.Qh15.chRep μ g a = (μ g : E) * a :=
    fun μ a => rfl
  have hact : ∀ (μ : G →* Eˣ) (a : E) (b : B),
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep μ) g (a ⊗ₜ[Qp] b) =
        ((μ g : E) * a) ⊗ₜ[Qp] PD.actB g b := by
    intro μ a b
    rw [← hch]
    rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
    | tmul c d =>
      have hu : (κ g : E) * a * ((κ⁻¹ g : E) * c) = ((1 : G →* Eˣ) g : E) * (a * c) := by
        rw [mul_mul_mul_comm, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel,
          MonoidHom.one_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, hact, hact, hact,
        Algebra.TensorProduct.tmul_mul_tmul, hu, map_mul]
