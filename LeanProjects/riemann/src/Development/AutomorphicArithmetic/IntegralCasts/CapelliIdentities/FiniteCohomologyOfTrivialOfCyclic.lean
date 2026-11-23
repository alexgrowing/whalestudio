import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteRoots
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChange
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicTrivialInductionRing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomologyFiniteShortExact
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CochainInjectiveExact

private theorem isDiscreteRep_of_forall_eq {k G : Type} [CommRing k] [Group G]
    [TopologicalSpace G] (A : Rep.{0, 0, 0} k G) (h : ∀ (g : G) (a : A.V), A.ρ g a = a) :
    GroundTheory.ProfCoh.IsDiscreteRep A := by
  haveI : A.ρ.IsTrivial := ⟨fun g => LinearMap.ext fun a => h g a⟩
  infer_instance

theorem UpperTheory.Reformulated.B.Gua5.finite_cohomology_of_trivial_of_cyclic :
    ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : @IsTopologicalGroup H inst_1 inst] (n r : Nat),
      (∀
          (C :
            @Rep.{0, 0, 0} (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)))
          [inst_3 : @GroundTheory.ProfCoh.IsDiscreteRep (ULift.{0, 0} Int) H (@ULift.commRing Int Int.instCommRing) inst inst_1 C]
          [Finite
              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)]
          [@IsAddCyclic
              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
              (@ZSMul.toSMul
                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                (@SubNegMonoid.toZSMul
                  (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                  (@AddGroup.toSubNegMonoid
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@AddCommGroup.toAddGroup
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)))))],
          (∀ (g : H)
              (c :
                @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C),
              @Eq
                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                (@DFunLike.coe
                  (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                    (@ULift.semiring Int Int.instSemiring)
                    (@RingHom.id (ULift.{0, 0} Int)
                      (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                  (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                  (fun
                      (x :
                        @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C) ↦
                    @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                  (@LinearMap.instFunLike (ULift.{0, 0} Int) (ULift.{0, 0} Int)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@ULift.semiring Int Int.instSemiring) (@ULift.semiring Int Int.instSemiring)
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@RingHom.id (ULift.{0, 0} Int)
                      (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring))))
                  (@DFunLike.coe
                    (@Representation (ULift.{0, 0} Int) H
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@ULift.semiring Int Int.instSemiring) (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst))
                      (@AddCommGroup.toAddCommMonoid
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                      (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                    H
                    (fun (x : H) ↦
                      @LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                        (@ULift.semiring Int Int.instSemiring)
                        (@RingHom.id (ULift.{0, 0} Int)
                          (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                    (@MonoidHom.instFunLike H
                      (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                        (@ULift.semiring Int Int.instSemiring)
                        (@RingHom.id (ULift.{0, 0} Int)
                          (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                      (@MulOneClass.toMulOne H
                        (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst))))
                      (@MulOneClass.toMulOne
                        (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                          (@ULift.semiring Int Int.instSemiring)
                          (@RingHom.id (ULift.{0, 0} Int)
                            (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@AddCommGroup.toAddCommMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                          (@AddCommGroup.toAddCommMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                          (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                        (@MulZeroOneClass.toMulOneClass
                          (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                            (@ULift.semiring Int Int.instSemiring)
                            (@RingHom.id (ULift.{0, 0} Int)
                              (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@AddCommGroup.toAddCommMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                            (@AddCommGroup.toAddCommMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                            (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                          (@instMulZeroOneClassOfSemiring
                            (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                              (@ULift.semiring Int Int.instSemiring)
                              (@RingHom.id (ULift.{0, 0} Int)
                                (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@AddCommGroup.toAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                              (@AddCommGroup.toAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                              (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                            (@Module.End.instSemiring (ULift.{0, 0} Int)
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@ULift.semiring Int Int.instSemiring)
                              (@AddCommGroup.toAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))
                              (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))))))
                    (@Rep.ρ (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    g)
                  c)
                c) →
            (∀
                (c :
                  @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C),
                @Eq
                  (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                  (@HSMul.hSMul Nat
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (@instHSMul Nat
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@NSMul.toSMul
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@AddMonoid.toNSMul
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@SubNegMonoid.toAddMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@AddGroup.toSubNegMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@AddCommGroup.toAddGroup
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)))))))
                    n c)
                  (@OfNat.ofNat
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                    (nat_lit 0)
                    (@Zero.toOfNat0
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                      (@NegZeroClass.toZero
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                        (@SubNegZeroMonoid.toNegZeroClass
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                          (@SubtractionMonoid.toSubNegZeroMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                            (@SubtractionCommMonoid.toSubtractionMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                              (@AddCommGroup.toDivisionAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) C))))))))) →
              Finite
                (@ModuleCat.carrier (ULift.{0, 0} Int)
                  (@CommRing.toRing (ULift.{0, 0} Int) (@ULift.commRing Int Int.instCommRing))
                  (@GroundTheory.ProfCoh.cohomology (ULift.{0, 0} Int) H (@ULift.commRing Int Int.instCommRing) inst inst_1 inst_2
                    C inst_3 r))) →
        ∀
          (A :
            @Rep.{0, 0, 0} (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)))
          [inst_3 : @GroundTheory.ProfCoh.IsDiscreteRep (ULift.{0, 0} Int) H (@ULift.commRing Int Int.instCommRing) inst inst_1 A]
          [Finite
              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)],
          (∀ (g : H)
              (a :
                @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A),
              @Eq
                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                (@DFunLike.coe
                  (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                    (@ULift.semiring Int Int.instSemiring)
                    (@RingHom.id (ULift.{0, 0} Int)
                      (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                  (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                  (fun
                      (x :
                        @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A) ↦
                    @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                  (@LinearMap.instFunLike (ULift.{0, 0} Int) (ULift.{0, 0} Int)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@ULift.semiring Int Int.instSemiring) (@ULift.semiring Int Int.instSemiring)
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                    (@AddCommGroup.toAddCommMonoid
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@RingHom.id (ULift.{0, 0} Int)
                      (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring))))
                  (@DFunLike.coe
                    (@Representation (ULift.{0, 0} Int) H
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@ULift.semiring Int Int.instSemiring) (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst))
                      (@AddCommGroup.toAddCommMonoid
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                      (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                    H
                    (fun (x : H) ↦
                      @LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                        (@ULift.semiring Int Int.instSemiring)
                        (@RingHom.id (ULift.{0, 0} Int)
                          (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                    (@MonoidHom.instFunLike H
                      (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                        (@ULift.semiring Int Int.instSemiring)
                        (@RingHom.id (ULift.{0, 0} Int)
                          (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                        (@AddCommGroup.toAddCommMonoid
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                      (@MulOneClass.toMulOne H
                        (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst))))
                      (@MulOneClass.toMulOne
                        (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                          (@ULift.semiring Int Int.instSemiring)
                          (@RingHom.id (ULift.{0, 0} Int)
                            (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@AddCommGroup.toAddCommMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                          (@AddCommGroup.toAddCommMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                          (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                        (@MulZeroOneClass.toMulOneClass
                          (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                            (@ULift.semiring Int Int.instSemiring)
                            (@RingHom.id (ULift.{0, 0} Int)
                              (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@AddCommGroup.toAddCommMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                            (@AddCommGroup.toAddCommMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                            (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                          (@instMulZeroOneClassOfSemiring
                            (@LinearMap (ULift.{0, 0} Int) (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)
                              (@ULift.semiring Int Int.instSemiring)
                              (@RingHom.id (ULift.{0, 0} Int)
                                (@Semiring.toNonAssocSemiring (ULift.{0, 0} Int) (@ULift.semiring Int Int.instSemiring)))
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@AddCommGroup.toAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                              (@AddCommGroup.toAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                              (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                            (@Module.End.instSemiring (ULift.{0, 0} Int)
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@ULift.semiring Int Int.instSemiring)
                              (@AddCommGroup.toAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))
                              (@Rep.hV2 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))))))
                    (@Rep.ρ (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    g)
                  a)
                a) →
            (∀
                (a :
                  @Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A),
                @Eq
                  (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                    (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                  (@HSMul.hSMul Nat
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (@instHSMul Nat
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@NSMul.toSMul
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@AddMonoid.toNSMul
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@SubNegMonoid.toAddMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@AddGroup.toSubNegMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@AddCommGroup.toAddGroup
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)))))))
                    n a)
                  (@OfNat.ofNat
                    (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                    (nat_lit 0)
                    (@Zero.toOfNat0
                      (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                        (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                      (@NegZeroClass.toZero
                        (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                          (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                        (@SubNegZeroMonoid.toNegZeroClass
                          (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                            (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                          (@SubtractionMonoid.toSubNegZeroMonoid
                            (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                              (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                            (@SubtractionCommMonoid.toSubtractionMonoid
                              (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                              (@AddCommGroup.toDivisionAddCommMonoid
                                (@Rep.V (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A)
                                (@Rep.hV1 (ULift.{0, 0} Int) H (@ULift.semiring Int Int.instSemiring)
                                  (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst)) A))))))))) →
              Finite
                (@ModuleCat.carrier (ULift.{0, 0} Int)
                  (@CommRing.toRing (ULift.{0, 0} Int) (@ULift.commRing Int Int.instCommRing))
                  (@GroundTheory.ProfCoh.cohomology (ULift.{0, 0} Int) H (@ULift.commRing Int Int.instCommRing) inst inst_1 inst_2
                    A inst_3 r)) := by
  intro H _ _ _ n r hC A inst hfin htriv hn
  have hι : ∀ (B : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [GroundTheory.ProfCoh.IsDiscreteRep B],
      (∀ m : ℕ, Function.Injective ((GroundTheory.ProfCoh.cochainsComplexι B).f m).hom) ∧
      ∀ (m : ℕ) (x : (Fin m → H) → B.V),
        (∃ y, ((GroundTheory.ProfCoh.cochainsComplexι B).f m).hom y = x) ↔ IsLocallyConstant x := by
    intro B _
    refine ⟨fun m => Subtype.val_injective, fun m x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩
    rintro ⟨y, rfl⟩
    exact y.2
  refine UpperTheory.cyclic_trivial_induction n
    (fun B => ∀ [GroundTheory.ProfCoh.IsDiscreteRep B], Finite (GroundTheory.ProfCoh.cohomology B r))
    ?_ ?_ A hfin htriv hn
  · intro C _ _ h1 h2 _
    exact hC C h1 h2
  · intro A B C f g hA hC' hf hfg hg PA PC _
    haveI := isDiscreteRep_of_forall_eq A hA
    haveI := isDiscreteRep_of_forall_eq C hC'
    obtain ⟨φ, ψ, w, hS⟩ := UpperTheory.cochain_injective_exact A B C f g _ _ _ (GroundTheory.ProfCoh.cochainsComplexι A)
      (GroundTheory.ProfCoh.cochainsComplexι B) (GroundTheory.ProfCoh.cochainsComplexι C) hf hfg hg
      (hι A).1 (hι B).1 (hι C).1 (hι A).2 (hι B).2 (hι C).2
    exact (UpperTheory.homology_finite_short_exact hS r).1 PA PC
