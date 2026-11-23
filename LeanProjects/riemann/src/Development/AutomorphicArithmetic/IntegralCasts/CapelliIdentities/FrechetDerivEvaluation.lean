import Mathlib

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.FrechetDerivEvaluation.aux {σ : Type*} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i : σ, eval z (pderiv i g) • (ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ)) z := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a z
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact h
  | mul_X p n hp =>
    have h := hp.mul (hasFDerivAt_apply (𝕜 := ℂ) n z)
    simp only [map_mul, eval_X]
    refine HasFDerivAt.congr_fderiv h ?_
    ext v
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib, apply_ite (eval z), mul_assoc, mul_comm, mul_left_comm]

theorem UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval.{u_1} :
    ∀ {σ : Type u_1} [inst : Fintype σ] (g : @MvPolynomial σ Complex Complex.instCommSemiring) (z : σ → Complex),
      @HasFDerivAt Complex (@DenselyNormedField.toNontriviallyNormedField Complex Complex.instDenselyNormedField)
        (σ → Complex) (@Pi.addCommGroup σ (fun (a : σ) ↦ Complex) fun (i : σ) ↦ Complex.addCommGroup)
        (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
          fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
        (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
          @UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
        Complex Complex.addCommGroup (@Semiring.toModule Complex Complex.instSemiring)
        (@UniformSpace.toTopologicalSpace Complex
          (@PseudoMetricSpace.toUniformSpace Complex
            (@SeminormedRing.toPseudoMetricSpace Complex
              (@SeminormedCommRing.toSeminormedRing Complex
                (@NormedCommRing.toSeminormedCommRing Complex
                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
        (fun (x : σ → Complex) ↦
          @DFunLike.coe
            (@RingHom (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
              (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
            (@MvPolynomial σ Complex Complex.instCommSemiring)
            (fun (x : @MvPolynomial σ Complex Complex.instCommSemiring) ↦ Complex)
            (@RingHom.instFunLike (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
              (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
            (@MvPolynomial.eval Complex σ Complex.instCommSemiring x) g)
        (∑ i : σ,
          @HSMul.hSMul Complex
            (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
              (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                @UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              Complex.instAddCommMonoid
              (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
              (@Semiring.toModule Complex Complex.instSemiring))
            (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
              (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                @UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              Complex.instAddCommMonoid
              (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
              (@Semiring.toModule Complex Complex.instSemiring))
            (@instHSMul Complex
              (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
                (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                  @UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
                (@UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                Complex.instAddCommMonoid
                (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                  fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
                (@Semiring.toModule Complex Complex.instSemiring))
              (@ContinuousLinearMap.instSMul Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
                (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                  @UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
                (@UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                Complex.instAddCommMonoid
                (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                  fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
                (@Semiring.toModule Complex Complex.instSemiring) Complex
                (@NonUnitalNonAssocSemiring.toDistribSMul Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))))
                (@Algebra.to_smulCommClass Complex Complex Complex.instCommSemiring
                  (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                  (@Algebra.id Complex Complex.instCommSemiring))
                (@SeparatelyContinuousMul.to_continuousSMul Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                  Complex.instMul
                  (@IsSemitopologicalSemiring.toSeparatelyContinuousMul Complex
                    (@UniformSpace.toTopologicalSpace Complex
                      (@PseudoMetricSpace.toUniformSpace Complex
                        (@SeminormedRing.toPseudoMetricSpace Complex
                          (@SeminormedCommRing.toSeminormedRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    (@IsSemitopologicalRing.toIsSemitopologicalSemiring Complex
                      (@UniformSpace.toTopologicalSpace Complex
                        (@PseudoMetricSpace.toUniformSpace Complex
                          (@SeminormedRing.toPseudoMetricSpace Complex
                            (@SeminormedCommRing.toSeminormedRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))
                      (@IsTopologicalRing.toIsSemitopologicalRing Complex
                        (@UniformSpace.toTopologicalSpace Complex
                          (@PseudoMetricSpace.toUniformSpace Complex
                            (@SeminormedRing.toPseudoMetricSpace Complex
                              (@SeminormedCommRing.toSeminormedRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))
                        (@IsTopologicalDivisionRing.toIsTopologicalRing Complex
                          (@Field.toDivisionRing Complex Complex.instField)
                          (@UniformSpace.toTopologicalSpace Complex
                            (@PseudoMetricSpace.toUniformSpace Complex
                              (@SeminormedRing.toPseudoMetricSpace Complex
                                (@SeminormedCommRing.toSeminormedRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                          (@NormedDivisionRing.to_isTopologicalDivisionRing Complex
                            (@NormedField.toNormedDivisionRing Complex Complex.instNormedField)))))))))
            (@DFunLike.coe
              (@RingHom (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
                (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                  (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
                (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
              (@MvPolynomial σ Complex Complex.instCommSemiring)
              (fun (x : @MvPolynomial σ Complex Complex.instCommSemiring) ↦ Complex)
              (@RingHom.instFunLike (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
                (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                  (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
                (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
              (@MvPolynomial.eval Complex σ Complex.instCommSemiring z)
              (@DFunLike.coe
                (@Derivation Complex (@MvPolynomial σ Complex Complex.instCommSemiring)
                  (@MvPolynomial σ Complex Complex.instCommSemiring) Complex.instCommSemiring
                  (@AddMonoidAlgebra.commSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    Complex.instCommSemiring (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))
                  (@AddMonoidAlgebra.instAddCommMonoid Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
                  (@AddMonoidAlgebra.algebra Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Algebra.id Complex Complex.instCommSemiring)
                    (@AddCommMonoid.toAddMonoid (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                      (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid)))
                  (@Semiring.toModule (@MvPolynomial σ Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring (@MvPolynomial σ Complex Complex.instCommSemiring)
                      (@AddMonoidAlgebra.commSemiring Complex
                        (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                        (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))))
                  (@AddMonoidAlgebra.instModule Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Semiring.toModule Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))))
                (@MvPolynomial σ Complex Complex.instCommSemiring)
                (fun (x : @MvPolynomial σ Complex Complex.instCommSemiring) ↦
                  @MvPolynomial σ Complex Complex.instCommSemiring)
                (@Derivation.instFunLike Complex (@MvPolynomial σ Complex Complex.instCommSemiring)
                  (@MvPolynomial σ Complex Complex.instCommSemiring) Complex.instCommSemiring
                  (@AddMonoidAlgebra.commSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    Complex.instCommSemiring (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))
                  (@AddMonoidAlgebra.instAddCommMonoid Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
                  (@AddMonoidAlgebra.algebra Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Algebra.id Complex Complex.instCommSemiring)
                    (@AddCommMonoid.toAddMonoid (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                      (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid)))
                  (@Semiring.toModule (@MvPolynomial σ Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring (@MvPolynomial σ Complex Complex.instCommSemiring)
                      (@AddMonoidAlgebra.commSemiring Complex
                        (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                        (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))))
                  (@AddMonoidAlgebra.instModule Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Semiring.toModule Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))))
                (@MvPolynomial.pderiv Complex σ Complex.instCommSemiring i) g))
            (@ContinuousLinearMap.proj Complex Complex.instSemiring σ (fun (x : σ) ↦ Complex)
              (fun (i : σ) ↦
                @UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              (fun (i : σ) ↦ Complex.instAddCommMonoid) (fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring) i))
        z := by
  intro σ _ g z
  exact UpperTheory.Reformulated.B.FrechetDerivEvaluation.aux g z
