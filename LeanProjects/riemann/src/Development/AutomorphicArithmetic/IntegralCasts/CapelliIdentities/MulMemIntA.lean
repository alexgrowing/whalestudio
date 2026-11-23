import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Uc13.Af :
    (F : Type) → [inst : Field F] → [@NumberField F inst] → Type :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst] ↦
      @IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
        (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F
        inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Uc13.Fv :
    (F : Type) →
      [inst : Field F] →
        [@NumberField F inst] →
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst) →
            Type :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
        (v :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
        (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F
        inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v

theorem UpperTheory.Reformulated.B.Uc13.aux3 :
    ∀ (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
      (i :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst)),
      @SubringClass
        (@ValuationSubring
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
        (@NonAssocCommRing.toNonAssocRing
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
          (@CommRing.toNonAssocCommRing
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (@Field.toCommRing
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))))
        (@ValuationSubring.instSetLike
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)) := by
  intro F _ _ i
  infer_instance

theorem UpperTheory.Reformulated.B.Uc13.aux4 :
    ∀ (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
      (v :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst))
      (x : F),
      @Eq (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
        (@OneHom.toFun
          (@RestrictedProduct
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @SetLike.coe
                (@ValuationSubring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@ValuationSubring.instSetLike
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
            (@Filter.cofinite
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
          (@MulOne.toOne
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))))))
          (@MulOne.toOne
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))))))
          (@MonoidHom.toOneHom
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1)))))))
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))))
            (@RingHom.toMonoidHom
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@Semiring.toNonAssocSemiring
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@Ring.toSemiring
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@RestrictedProduct.instRingCoeOfSubringClass
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (w :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                    (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
              (@Semiring.toNonAssocSemiring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@Ring.toSemiring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))
              (@RestrictedProduct.evalRingHom
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (w :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                v
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
          (@DFunLike.coe
            (@RingHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            F (fun (x : F) ↦ @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@RingHom.instFunLike F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            (@Algebra.algebraMap F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            x))
        (@OneHom.toFun
          (@RestrictedProduct
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @SetLike.coe
                (@ValuationSubring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@ValuationSubring.instSetLike
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
            (@Filter.cofinite
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
          (@MulOne.toOne
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))))))
          (@MulOne.toOne
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))))))
          (@MonoidHom.toOneHom
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1)))))))
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))))
            (@RingHom.toMonoidHom
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@Semiring.toNonAssocSemiring
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@Ring.toSemiring
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@RestrictedProduct.instRingCoeOfSubringClass
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (w :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                    (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
              (@Semiring.toNonAssocSemiring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@Ring.toSemiring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))
              (@RestrictedProduct.evalRingHom
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (w :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                v
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
          (@DFunLike.coe
            (@RingHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            F (fun (x : F) ↦ @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@RingHom.instFunLike F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            (@Algebra.algebraMap F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            x)) := by
  intro F _ _ v x
  rfl

noncomputable def UpperTheory.Reformulated.B.Uc13.evalV :
    (F : Type) →
      [inst : Field F] →
        [inst_1 : @NumberField F inst] →
          (v :
              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)) →
            @AlgHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                  (@Field.toSemifield (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
              (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F F inst
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v
                (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))) :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
        (v :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      let __src :
        @RingHom
          (@RestrictedProduct
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @SetLike.coe
                (@ValuationSubring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@ValuationSubring.instSetLike
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
            (@Filter.cofinite
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
          (@Semiring.toNonAssocSemiring
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@Ring.toSemiring
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@RestrictedProduct.instRingCoeOfSubringClass
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (w :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
          (@Semiring.toNonAssocSemiring
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@Ring.toSemiring
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@DivisionRing.toRing
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@Field.toDivisionRing
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))) :=
        @RestrictedProduct.evalRingHom
          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst))
          (fun
              (w :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
          (@Filter.cofinite
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)))
          (fun
              (i :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @ValuationSubring
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
          (fun
              (i :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @ValuationSubring.instSetLike
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
          v
          (fun
              (i :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @DivisionRing.toRing
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@Field.toDivisionRing
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
          (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1);
      @AlgHom.mk F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
        (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
          (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
            (@Field.toSemifield (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
        (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F F inst (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@NumberField.RingOfIntegers.instAlgebra_1 F inst) (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)
          v (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
        __src (@UpperTheory.Reformulated.B.Uc13.aux4 F inst inst_1 v)

noncomputable def UpperTheory.Reformulated.B.Uc13.intAf :
    (F : Type) → [inst : Field F] → [inst_1 : @NumberField F inst] → Set (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst] ↦
      @Set.ofPred (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) fun (a : @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) ↦
        ∀
          (v :
            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)),
          @Membership.mem (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
            (@ValuationSubring
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))
            (@SetLike.instMembership
              (@ValuationSubring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@ValuationSubring.instSetLike
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@DFunLike.coe
              (@AlgHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                  (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                    (@Field.toSemifield (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F F inst
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v
                  (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))))
              (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (fun (x : @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) ↦ @UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
              (@AlgHom.funLike F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                  (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                    (@Field.toSemifield (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F F inst
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v
                  (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))))
              (@UpperTheory.Reformulated.B.Uc13.evalV F inst inst_1 v) a)

noncomputable def UpperTheory.Reformulated.B.Uc13.intA :
    (F E : Type) →
      [inst : Field F] →
        [inst_1 : @NumberField F inst] →
          [inst_2 : Field E] →
            [inst_3 :
                @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))] →
              @AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_3))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_3))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_3))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_3))) :=
    fun (F E : Type) [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field E]
        [inst_3 :
          @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))] ↦
      @AddSubgroup.closure
        (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
          (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
          (@Semiring.toAddCommMonoid E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
          (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
            (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_3))
        (@AddGroupWithOne.toAddGroup
          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
            (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
            (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_3))
          (@Ring.toAddGroupWithOne
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_3))
            (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_3)))
        (@Set.ofPred
          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
            (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
            (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_3))
          fun
            (y :
              @TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                  inst_3)) ↦
          ∃ (a : @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1),
            And
              (@Membership.mem (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (Set (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1))
                (@Set.instMembership (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)) (@UpperTheory.Reformulated.B.Uc13.intAf F inst inst_1) a)
              (∃ (x : @NumberField.RingOfIntegers E inst_2),
                @Eq
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_3))
                  y
                  (@TensorProduct.tmul F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_3)
                    a (@NumberField.RingOfIntegers.val E inst_2 x))))

private theorem UpperTheory.Reformulated.B.Uc13.intAf_mul (F : Type) [Field F] [NumberField F]
    {a b : UpperTheory.Reformulated.B.Uc13.Af F} (ha : a ∈ UpperTheory.Reformulated.B.Uc13.intAf F)
    (hb : b ∈ UpperTheory.Reformulated.B.Uc13.intAf F) : a * b ∈ UpperTheory.Reformulated.B.Uc13.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem UpperTheory.Reformulated.B.Uc13.mul_mem_intA :
    ∀ (F E : Type) [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field E] [@NumberField E inst_2]
      [inst_4 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
      {x y :
        @TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
          (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
          (@Semiring.toAddCommMonoid E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
          (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
            (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)},
      @Membership.mem
          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
            (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
            (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
          (@AddSubgroup
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddGroupWithOne.toAddGroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@Ring.toAddGroupWithOne
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                  inst_4))))
          (@SetLike.instMembership
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup.instSetLike
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4)))))
          (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4) x →
        @Membership.mem
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@SetLike.instMembership
              (@AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddSubgroup.instSetLike
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)))))
            (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4) y →
          @Membership.mem
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@SetLike.instMembership
              (@AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddSubgroup.instSetLike
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)))))
            (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4)
            (@HMul.hMul
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@instHMul
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Algebra.TensorProduct.instMul F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toNonUnitalCommRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.to_smulCommClass F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring
                      (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@CommRing.toCommSemiring
                        (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@IsScalarTower.right F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring
                      (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@CommRing.toCommSemiring
                        (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                        (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_2)))))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)
                  (@Algebra.to_smulCommClass F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)
                  (@IsScalarTower.right F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4)))
              x y) := by
  intro F E _ _ _ _ _ x y hx hy
  unfold UpperTheory.Reformulated.B.Uc13.intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure
      ⟨a * b, UpperTheory.Reformulated.B.Uc13.intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h
